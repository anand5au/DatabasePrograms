package iterator;

import java.io.IOException;
import java.util.ArrayList;

import bufmgr.PageNotReadException;
import global.AttrOperator;
import global.AttrType;
import global.GlobalConst;
import global.TupleOrder;
import heap.Heapfile;
import heap.InvalidTupleSizeException;
import heap.InvalidTypeException;
import heap.Tuple;
import index.IndexException;

public class IEJoinWithFilter extends Iterator implements GlobalConst 
{

	 private AttrType  _in1[], _in2[];
	  private  int        in1_len, in2_len;
	  private  Sort  p_r1, p_s1,        // pointers to the two iterators. If the
	    p_r2, p_s2, baser1, baser2, bases1, bases2;               // inputs are sorted, then no sorting is done
	  private  TupleOrder  _order, _order2;                      // The sorting order.
	  private  CondExpr  OutputFilter[];
	  
	  private  boolean      get_from_in1, get_from_in2;        // state variables for get_next
	  private  int        jc_in1, jc_in2;
	  private  boolean        process_next_block;
	  private  short     inner_str_sizes[];
	  private  IoBuf    io_buf1,  io_buf2;
	  private  Tuple     TempTuple1,  TempTuple2;
	  private  Tuple     tuple1,  tuple2;
	  private  boolean       done;
	  private  byte    _bufs1[][],_bufs2[][];
	  private  int        _n_pages; 
	  private  Heapfile temp_file_fd1, temp_file_fd2;
	  private  AttrType   sortFldType;
	  private  int        t1_size, t2_size;
	  private  Tuple     Jtuple;
	  private  FldSpec   perm_mat[];
	  private  int        nOutFlds;
	  private int joinvalue_in1, joinvalue_in2;
	  private ArrayList<Integer> joinlist_in1 = new ArrayList<Integer>();
	  private ArrayList<Integer> P = new ArrayList<Integer>();
	  private ArrayList<Integer> Pd = new ArrayList<Integer>();
	  private ArrayList<Integer> O1 = new ArrayList<Integer>();
	  private ArrayList<Integer> O2 = new ArrayList<Integer>();
	  private ArrayList<Integer> bitarray =  new ArrayList<Integer>();
	  private ArrayList<Integer> bloomingFilter = new ArrayList<Integer>();
	  private int chunk_size = 32;
	  private int bitsize;
	  private int operator1 = -1;
	  private int operator2 = -1;
	  private int equalityOffset = -1; 
	  private int outer=0, inner=0, in = 0, filterIdx=0, chunkIdx=0;
	  private boolean flag1, flag2;
	  private ArrayList<Tuple> L1 = new ArrayList<Tuple>();
	  private ArrayList<Tuple> L2 = new ArrayList<Tuple>();
	  private ArrayList<Tuple> L1d = new ArrayList<Tuple>();
	  private ArrayList<Tuple> L2d = new ArrayList<Tuple>();
	  private int flag = 0, offset1, offset2;
	  
	public IEJoinWithFilter(AttrType    in1[],               
			   int     len_in1,                        
			   short   s1_sizes[],
			   AttrType    in2[],                
			   int     len_in2,                        
			   short   s2_sizes[],
			   
			   int     join_col_in1,                
			   int      sortFld1Len,
			   int     join_col_in2,                
			   int      sortFld2Len,
			   int     amt_of_mem,               
			   Iterator     amr1,                
			   Iterator     ams1,    
			   Iterator     amr2,                
			   Iterator     ams2,
			   boolean     in1_sorted,                
			   boolean     in2_sorted,                
			   TupleOrder order1,
			   TupleOrder order2,
			   
			   CondExpr  outFilter[],                
			   FldSpec   proj_list[],
			   int       n_out_flds,
			   int chunkSize
			   )
	    throws JoinsException, IndexException, InvalidTupleSizeException, InvalidTypeException, PageNotReadException, PredEvalException, LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception
	    {
			chunk_size = chunkSize;
		  	_in1 = new AttrType[in1.length];
		  	_in2 = new AttrType[in2.length];
		  	System.arraycopy(in1,0,_in1,0,in1.length);
		  	System.arraycopy(in2,0,_in2,0,in2.length);
		  	in1_len = len_in1;
		  	in2_len = len_in2;
		  	operator1 = outFilter[0].op.attrOperator;
		  	operator2 = outFilter[1].op.attrOperator;
		  	flag1 = true;
		  	outer = 0;
		  	joinvalue_in1 = join_col_in1;
		  	joinvalue_in2 = join_col_in2;
		  	
		  	if((operator1 == AttrOperator.aopLE || operator1 == AttrOperator.aopGE) && 
		  			(operator2 == AttrOperator.aopLE || operator2 == AttrOperator.aopGE))
		  	{
		  		equalityOffset = 0;
		  	}
		  	else
		  	{
		  		equalityOffset = 1;
		  	}
		  	Jtuple = new Tuple();
		  	AttrType[] Jtypes = new AttrType[n_out_flds];
		  	short[]    ts_size = null;
		  	perm_mat = proj_list;
		  	nOutFlds = n_out_flds;
		  	try 
		  	{
		  		ts_size = TupleUtils.setup_op_tuple(Jtuple, Jtypes,
		  				in1, len_in1, in2, len_in2,
						s1_sizes, s2_sizes, 
						proj_list,n_out_flds );
		  	}
		  	catch (Exception e)
		  	{
		  		throw new TupleUtilsException (e, "Exception is caught by SortMerge.java");
		  	}
	      
		  	int n_strs2 = 0;
	      
		  	for (int i = 0; i < len_in2; i++)
		  	{
		  		if (_in2[i].attrType == AttrType.attrString)
		  		{
		  			n_strs2++;
		  		}
		  	}
		  	inner_str_sizes = new short [n_strs2];
	    
		  	for (int i = 0; i < n_strs2; i++)
		  	{
		  		inner_str_sizes[i] = s2_sizes[i];
		  	}
	        
		  	p_r1 = null;
		  	p_r2 = null;
			p_s1 = null;
		  	p_s2 = null;
	      
		  	if (!in1_sorted)
		  	{
		  		try
		  		{
		  			p_r1 = new Sort(in1, (short)len_in1, s1_sizes, amr1, join_col_in1,
		  					order1, sortFld1Len, amt_of_mem / 2); //L1
		  			p_r2 = new Sort(in1, (short)len_in1, s1_sizes, amr2, join_col_in2,
		  					order2, sortFld1Len, amt_of_mem / 2); //L2
		  		}
		  		catch(Exception e)
		  		{
		  			throw new SortException (e, "Sort failed");
		  		}
		  	}
			
		  	if (!in2_sorted)
		  	{
		  		try 
		  		{
		  			p_s1 = new Sort(in2, (short)len_in2, s2_sizes, ams1, join_col_in1,
		  					order1, sortFld2Len, amt_of_mem / 2); // L1 dash
		  			p_s2 = new Sort(in2, (short)len_in2, s2_sizes, ams2, join_col_in2,
		  					order2, sortFld2Len, amt_of_mem / 2); // L2 dash
		  		}
		  		catch(Exception e)
		  		{
		  			throw new SortException (e, "Sort failed");
		  		}
		  	}
		  	
		  	baser1 = new Sort(p_r1);
		  	baser2 = new Sort(p_r2);
		  	bases1 = new Sort(p_s1);
		  	bases2 = new Sort(p_s2);
	      
		  	OutputFilter = outFilter;
		  	_order       = order1;
		  	_order2       = order2;
		  	jc_in1       = join_col_in1;
		  	jc_in2       = join_col_in2;
		  	get_from_in1 = true;
		  	get_from_in2 = true;
	      
		  	// open io_bufs
		  	io_buf1 = new IoBuf();
		  	io_buf2 = new IoBuf();
	      
		  	// Allocate memory for the temporary tuples
		  	TempTuple1 = new Tuple();
		  	TempTuple2 =  new Tuple();
		  	tuple1 = new Tuple();
		  	tuple2 =  new Tuple();
	      
	      
		  	if (io_buf1  == null || io_buf2  == null ||
		  			TempTuple1 == null || TempTuple2==null ||
		  			tuple1 ==  null || tuple2 ==null)
		  	{
		  		throw new JoinNewFailed ("SortMerge.java: allocate failed");
		  	}
		  	if ( amt_of_mem < 2 )
		  	{
		  		throw new JoinLowMemory ("SortMerge.java: memory not enough");
		  	}
	      
		  	try
		  	{
		  		TempTuple1.setHdr((short)in1_len, _in1, s1_sizes);
		  		tuple1.setHdr((short)in1_len, _in1, s1_sizes);
		  		TempTuple2.setHdr((short)in2_len, _in2, s2_sizes);
		  		tuple2.setHdr((short)in2_len, _in2, s2_sizes);
		  	}
		  	catch (Exception e)
		  	{
		  		throw new SortException (e,"Set header failed");
		  	}
		  	t1_size = tuple1.size();
		  	t2_size = tuple2.size();
	      
		  	process_next_block = true;
		  	done               = false;
	      
		  	// Two buffer pages to store equivalence classes
		  	// NOTE -- THESE PAGES ARE NOT OBTAINED FROM THE BUFFER POOL
		  	// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
		  	_n_pages = 1;
		  	_bufs1 = new byte [_n_pages][MINIBASE_PAGESIZE];
		  	_bufs2 = new byte [_n_pages][MINIBASE_PAGESIZE];
	     
	     
		  	temp_file_fd1 = null;
		  	temp_file_fd2 = null;
		  	try 
		  	{
		  		temp_file_fd1 = new Heapfile(null);
		  		temp_file_fd2 = new Heapfile(null);
		  	}
		  	catch(Exception e)
		  	{
		  		throw new SortException (e, "Create heap file failed");
		  	}
	      
		  	sortFldType = _in1[jc_in1-1];
		  	
		  	Tuple tupletmp;
		  	while(true)
		  	{
		  		tupletmp = new Tuple();
		  		if((tupletmp = p_r1.get_next())!=null)
		  		{
		  			L1.add(new Tuple(tupletmp));
		  		}
		  		else
		  			break;
		  	}
		  	/*for(int i=0;i<L1.size();i++)
		  	{
		  		System.out.println(L1.get(i).getIntFld(3));
		  	}
		  	System.out.println("------------");*/
		  	while(true)
		  	{
		  		tupletmp = new Tuple();
		  		if((tupletmp = p_r2.get_next())!=null)
		  		{
		  			L2.add(new Tuple(tupletmp));
		  		}
		  		else
		  			break;
		  	}
		  	/*for(int i=0;i<L2.size();i++)
		  	{
		  		System.out.println(L2.get(i).getIntFld(4));
		  	}
		  	System.out.println("------------");*/
			while(true)
		  	{
		  		tupletmp = new Tuple();
		  		if((tupletmp = p_s1.get_next())!=null)
		  		{
		  			L1d.add(new Tuple(tupletmp));
		  		}
		  		else
		  			break;
		  	}
			/*for(int i=0;i<L1d.size();i++)
		  	{
		  		System.out.println(L1d.get(i).getIntFld(3));
		  	}
			System.out.println("------------");*/
			while(true)
		  	{
		  		tupletmp = new Tuple();
		  		if((tupletmp = p_s2.get_next())!=null)
		  		{
		  			L2d.add(new Tuple(tupletmp));
		  		}
		  		else
		  			break;
		  	}
			/*for(int i=0;i<L2d.size();i++)
		  	{
		  		System.out.println(L2d.get(i).getIntFld(4));
		  	}
			System.out.println("------------");*/
			
			// Compute Permutation Arrays P and Pd
			
			for(int i=0;i<L2.size();i++)
		  	{
		  		for(int j=0;j<L1.size();j++)
		  		{
		  			if(L2.get(i).getIntFld(joinvalue_in1) == L1.get(j).getIntFld(joinvalue_in1))
		  			{
		  				P.add(j);
		  			}
		  		}
		  	}
			
			//System.out.println(P);
			for(int i=0;i<L2d.size();i++)
		  	{
		  		for(int j=0;j<L1d.size();j++)
		  		{
		  			if(L2d.get(i).getIntFld(joinvalue_in1) == L1d.get(j).getIntFld(joinvalue_in1))
		  			{
		  				Pd.add(j);
		  			}
		  		}
		  	}
			//System.out.println(Pd);
			
			// Create Offset arrays
			for(int i=0;i<L1.size();i++)
		  	{
				int j;
		  		for(j=0;j<L1d.size();j++)
		  		{
		  			if(order1.tupleOrder == 0)
		  			{
		  				if(L1.get(i).getIntFld(joinvalue_in1) == L1d.get(j).getIntFld(joinvalue_in1))
			  			{
			  				break;
			  			}
			  			else if(L1d.get(j).getIntFld(joinvalue_in1) > L1.get(i).getIntFld(joinvalue_in1))
			  			{
			  				break;
			  			}
		  			}
		  			else
		  			{
		  				if(L1.get(i).getIntFld(joinvalue_in1) == L1d.get(j).getIntFld(joinvalue_in1))
			  			{
			  				break;
			  			}
			  			else if(L1d.get(j).getIntFld(joinvalue_in1) < L1.get(i).getIntFld(joinvalue_in1))
			  			{
			  				break;
			  			}
		  			}
		  		}
		  		O1.add(j);
		  	}
			//System.out.println(O1);
			
			for(int i=0;i<L2.size();i++)
		  	{
				int j;
		  		for(j=0;j<L2d.size();j++)
		  		{
		  			if(order2.tupleOrder == 0)
		  			{
		  				if(L2.get(i).getIntFld(joinvalue_in2) == L2d.get(j).getIntFld(joinvalue_in2))
			  			{
			  				break;
			  			}
			  			else if(L2d.get(j).getIntFld(joinvalue_in2) > L2.get(i).getIntFld(joinvalue_in2))
			  			{
			  				break;
			  			}
		  			}
		  			else
		  			{
		  				if(L2.get(i).getIntFld(joinvalue_in2) == L2d.get(j).getIntFld(joinvalue_in2))
			  			{
			  				break;
			  			}
			  			else if(L2d.get(j).getIntFld(joinvalue_in2) < L2.get(i).getIntFld(joinvalue_in2))
			  			{
			  				break;
			  			}
		  			}
		  		}
		  		O2.add(j);
		  	}
			//System.out.println(O2);
			bitarray = new ArrayList<Integer>();
			for(int i=0;i<L1d.size();i++)
			{
				bitarray.add(i, 0);
			}
			//System.out.println(bitarray);
			bitsize = bitarray.size();
			
			int filterSize = (bitarray.size()/chunk_size) + 1;
		  	for (int i = 0; i < filterSize; i++) {
		  		bloomingFilter.add(0);
		  	}
	    }

	@Override
	public Tuple get_next() throws IOException, JoinsException, IndexException, InvalidTupleSizeException,
			InvalidTypeException, PageNotReadException, TupleUtilsException, PredEvalException, SortException,
			LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception 
	{
		while(true)
		{
			if(outer >= L1.size())
				return null;
			
			if(flag == 0)
			{
				offset2 = O2.get(outer) >= bitsize ? bitsize-1 : O2.get(outer);
				inner = 0;
				while(inner <= offset2)
				{
					filterIdx = Pd.get(inner)/chunk_size;
					bloomingFilter.set(filterIdx, 1);
					bitarray.set(Pd.get(inner),1);
					inner++;
				}
				offset1 = O1.get(P.get(outer)) > bitsize ? bitsize : O1.get(P.get(outer));
				flag++;
				in = offset1+equalityOffset;
				chunkIdx = in % chunk_size;
				filterIdx = in/chunk_size;
			}
			
			if(filterIdx < bloomingFilter.size())
			{
  				if(bloomingFilter.get(filterIdx) == 1)
  				{
  					Tuple Rtuple = null;
					if(in < bitsize && chunkIdx < chunk_size)
					{
						if(bitarray.get(in) == 1)
						{
							Rtuple = new Tuple();
	  					  	AttrType types[] = {new AttrType(1), new AttrType(1)}; 
	  					  	Rtuple.setHdr((short) 2, types, inner_str_sizes);
	  						Rtuple.setIntFld(1, L2.get(outer).getIntFld(perm_mat[0].offset));
	  						Rtuple.setIntFld(2, L2d.get(in).getIntFld(perm_mat[0].offset));
						}
						in++;
						chunkIdx++;
					}
					if(in == bitsize)
					{
						outer++;
						flag = 0;
					}
					if(chunkIdx == chunk_size)
	  				{
	  					filterIdx++;
	  					chunkIdx = 0;
	  				}
					if(Rtuple != null)
	  					return Rtuple;
  				}
  				else
  				{
  					filterIdx++;
  					chunkIdx = 0;
  					in = filterIdx * chunk_size;
  					if(in >= bitarray.size())
  					{
  						outer++;
						flag = 0;
  					}
  				}
			}
		}
	}

	@Override
	public void close() throws IOException, JoinsException, SortException, IndexException {
		// TODO Auto-generated method stub
		
	}

}
