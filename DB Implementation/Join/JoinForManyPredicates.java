package iterator;

import heap.*;
import global.*;
import diskmgr.*;
import bufmgr.*;
import index.*;
import java.io.*;
import java.util.ArrayList;
import java.util.LinkedHashSet;

public class JoinForManyPredicates extends Iterator implements GlobalConst {
	  private AttrType  _in1[], _in2[];
	  private  int        in1_len, in2_len;
	  private  Sort  p_i1,        // pointers to the two iterators. If the
	    p_i2, base1, base2;               // inputs are sorted, then no sorting is done
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
	  private LinkedHashSet<Integer> permSet = new LinkedHashSet<Integer>();
	  private  AttrType   sortFldType;
	  private  int        t1_size, t2_size;
	  private  Tuple     Jtuple;
	  private  FldSpec   perm_mat[];
	  private  int        nOutFlds;
	  private int joinvalue_in1, joinvalue_in2;
	  private ArrayList<Integer> joinlist_in1 = new ArrayList<Integer>();
	  private ArrayList<Integer> permutation = new ArrayList<Integer>();
	  private ArrayList<Integer> bitarray =  new ArrayList<Integer>();
	  private int operator1 = -1;
	  private int operator2 = -1;
	  private int equalityOffset = -1; 
	  private int outer, inner;
	  private boolean flag1, flag2;
	  private ArrayList<Tuple> L1 = new ArrayList<Tuple>();
	  private ArrayList<Tuple> L2 = new ArrayList<Tuple>();
	  private int flag = 0;
	  /**
	   *constructor,initialization
	   *@param in1[]   Array containing field types of R
	   *@param len_in1  # of columns in R
	   *@param s1_sizes  shows the length of the string fields in R.
	   *@param in2[]  Array containing field types of S
	   *@param len_in2  # of columns in S
	   *@param s2_sizes shows the length of the string fields in S
	   *@param sortFld1Len the length of sorted field in R
	   *@param sortFld2Len the length of sorted field in S
	   *@param join_col_in1  The col of R to be joined with S
	   *@param join_col_in2  the col of S to be joined with R
	   *@param amt_of_mem   IN PAGES
	   *@param am1  access method for left input to join
	   *@param am2  access method for right input to join
	   *@param in1_sorted  is am1 sorted?
	   *@param in2_sorted  is am2 sorted?
	   *@param order the order of the tuple: assending or desecnding?
	   *@param outFilter[]  Ptr to the output filter
	   *@param proj_list shows what input fields go where in the output tuple
	   *@param n_out_flds number of outer relation fileds
	 * @throws Exception 
	 * @throws UnknownKeyTypeException 
	 * @throws UnknowAttrType 
	 * @throws LowMemException 
	 * @throws PredEvalException 
	 * @throws PageNotReadException 
	 * @throws InvalidTypeException 
	 * @throws InvalidTupleSizeException 
	 * @throws IndexException 
	 * @throws JoinsException 
	   */
	  public JoinForManyPredicates(AttrType    in1[],               
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
			   Iterator     am1,                
			   Iterator     am2,                
			   boolean     in1_sorted,                
			   boolean     in2_sorted,                
			   TupleOrder order1,
			   TupleOrder order2,
			   
			   CondExpr  outFilter[],                
			   FldSpec   proj_list[],
			   int       n_out_flds
			   )
	    throws JoinsException, IndexException, InvalidTupleSizeException, InvalidTypeException, PageNotReadException, PredEvalException, LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception
			   
	    {
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
	        
		  	p_i1 = null;
		  	p_i2 = null;
	      
		  	if (!in1_sorted)
		  	{
		  		try
		  		{
		  			p_i1 = new Sort(in1, (short)len_in1, s1_sizes, am1, join_col_in1,
		  					order1, sortFld1Len, amt_of_mem / 2);
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
		  			p_i2 = new Sort(in2, (short)len_in2, s2_sizes, am2, join_col_in2,
		  					order2, sortFld2Len, amt_of_mem / 2);
		  		}
		  		catch(Exception e)
		  		{
		  			throw new SortException (e, "Sort failed");
		  		}
		  	}
		  	
		  	base1 = new Sort(p_i1);
		  	base2 = new Sort(p_i2);
	      
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
		  	
		  	/*while ((tuple1 = p_i1.get_next()) != null) 
		  	{
		  		joinvalue_in1 = tuple1.getIntFld(join_col_in1);
		  		joinlist_in1.add(joinvalue_in1);
		  	}*/

		  	Tuple tupletmp;
		  	int ti = 0;
		  	int tj = 0;
		  	int sorderingl1 = 0;
		  	int sorderingl2 = 0;
		  	if(((outFilter[0].op.attrOperator == 1 || outFilter[0].op.attrOperator == 2) && (outFilter[1].op.attrOperator == 1 || outFilter[1].op.attrOperator == 4)) ||
		  			((outFilter[0].op.attrOperator == 4 || outFilter[0].op.attrOperator == 5) && (outFilter[1].op.attrOperator == 2 || outFilter[1].op.attrOperator == 5)))
		  	{
		  		sorderingl1 = 1; // Ascending
		  	}
		  	else
		  	{
		  		sorderingl1 = 2; // Descending 
		  	}
		  	
		  	if(((outFilter[0].op.attrOperator == 1 || outFilter[0].op.attrOperator == 4) && (outFilter[1].op.attrOperator == 4 || outFilter[1].op.attrOperator == 5)) ||
		  			((outFilter[0].op.attrOperator == 2 || outFilter[0].op.attrOperator == 5) && (outFilter[1].op.attrOperator == 1 || outFilter[1].op.attrOperator == 2)))
		  	{
		  		sorderingl2 = 1; // Ascending
		  	}
		  	else
		  	{
		  		sorderingl2 = 2; // Descending 
		  	}
		  	int whilecount = 0;
		  	while(true)
		  	{
		  		tupletmp = new Tuple();
		  		if((tupletmp = p_i1.get_next())!=null)
		  		{
		  			whilecount++;
		  			if(flag == 0)
		  			{
		  			//	System.out.println("1 "+ti);
		  				L1.add(new Tuple(tupletmp));
		  				flag++;
		  			}
		  			else
		  			{
		  			//	System.out.println("2 "+ti);
		  				if(tupletmp.getIntFld(join_col_in1) != L1.get(tj-1).getIntFld(join_col_in1))
		  				{
		  					L1.add(new Tuple(tupletmp));
		  					ti = tj;
		  				}
		  				else
		  				{
		  					if(sorderingl1 == 1) // 1 
		  					{
		  						int j = ti;
			  					for(;j<L1.size();)
			  					{
			  						// Sort column 2 in ascending
			  						if(tupletmp.getIntFld(join_col_in2) > L1.get(j).getIntFld(join_col_in2))
			  						{
			  							j++;
			  						}
			  						else
			  						{
			  							break;
			  						}
			  					}
			  					L1.add(j, new Tuple(tupletmp));
			  					
		  					}
		  					else
		  					{
		  					//	System.out.println("Came here");
		  						int j = ti;
			  					for(;j<L1.size();)
			  					{
			  						// Sort column 2 in descending
			  						if(tupletmp.getIntFld(join_col_in2) < L1.get(j).getIntFld(join_col_in2))
			  						{
			  							j++;
			  						}
			  						else
			  						{
			  							break;
			  						}
			  					}
			  					L1.add(j, new Tuple(tupletmp));
		  					}
		  				}
		  			}
		  			
		  		//	System.out.println(tupletmp.getIntFld(1));
		  		}
		  		else
		  			break;
		  		tj++;
		  	}
		  //	System.out.println("While count "+whilecount);
	/*	  	for(int i=0;i<L1.size();i++)
		  	{
		  		System.out.println(L1.get(i).getIntFld(join_col_in1) + "  "+L1.get(i).getIntFld(join_col_in2));
		  	}
		  	
		  	System.out.println("---------");*/
		  	ti = 0;
		  	tj = 0;
		  	flag = 0;
			while(true)
		  	{
		  		tupletmp = new Tuple();
		  		if((tupletmp = p_i2.get_next())!=null)
		  		{
		  			if(flag == 0)
		  			{
		  			//	System.out.println("1 "+ti);
		  				L2.add(new Tuple(tupletmp));
		  				flag++;
		  			}
		  			else
		  			{
		  			//	System.out.println("2 "+ti);
		  				if(tupletmp.getIntFld(join_col_in2) != L2.get(tj-1).getIntFld(join_col_in2))
		  				{
		  					L2.add(new Tuple(tupletmp));
		  					ti = tj;
		  				}
		  				else
		  				{
		  					if(sorderingl2 == 1) // 1 
		  					{
		  						int j = ti;
			  					for(;j<L2.size();)
			  					{
			  						// Sort column 2 in ascending
			  						if(tupletmp.getIntFld(join_col_in1) > L2.get(j).getIntFld(join_col_in1))
			  						{
			  							j++;
			  						}
			  						else
			  						{
			  							break;
			  						}
			  					}
			  					L2.add(j, new Tuple(tupletmp));
			  					
		  					}
		  					else
		  					{
		  					//	System.out.println("Came here");
		  						int j = ti;
			  					for(;j<L2.size();)
			  					{
			  						// Sort column 2 in descending
			  						if(tupletmp.getIntFld(join_col_in1) < L2.get(j).getIntFld(join_col_in1))
			  						{
			  							j++;
			  						}
			  						else
			  						{
			  							break;
			  						}
			  					}
			  					L2.add(j, new Tuple(tupletmp));
		  					}
		  				}
		  			}
		  			
		  		//	System.out.println(tupletmp.getIntFld(1));
		  		}
		  		else
		  			break;
		  		tj++;
		  	}
		  	
	/*	  	for(int i=0;i<L2.size();i++)
		  	{
		  		System.out.println(L2.get(i).getIntFld(join_col_in1) + "  "+L2.get(i).getIntFld(join_col_in2));
		  	}*/
		  	
			int count =0;
			System.out.println(L2.size());
			System.out.println(L1.size());
		  	for(int i=0;i<L2.size();i++)
		  	{
		  		for(int j=0;j<L1.size();j++)
		  		{
		  			int L1s = 0, L2s = 0;
		  			for(int z=0;z<in1.length;z++)
		  			{
		  				L1s += L1.get(j).getIntFld(z+1);
		  				L2s += L2.get(i).getIntFld(z+1);
		  			}
		  			//System.out.println("L1s "+L1s+" L2s"+L2s);
		  			if(L2.get(i).getIntFld(join_col_in1) == L1.get(j).getIntFld(join_col_in1) 
		  					&& L2.get(i).getIntFld(join_col_in2) == L1.get(j).getIntFld(join_col_in2) && L1s == L2s)
		  			{
		  			//	System.out.println(" i "+i+" j "+j);
		  				permSet.add(j);
		  				count++;
		  			}
		  		}
		  	}
/*		  	while ((tuple2 = p_i2.get_next()) != null) {
		  		joinvalue_in2 = tuple2.getIntFld(join_col_in1);
		  		for (int i = 0 ; i < joinlist_in1.size(); i++) {
		  			if (joinlist_in1.get(i) == joinvalue_in2) {
		  				permutation.add(i);
		  			}
		  		}
		  	}*/
		  	
			java.util.Iterator<Integer> it = permSet.iterator();
		  	while(it.hasNext())
		  	{
		  		permutation.add(it.next());
		  	}
		  	for (int i = 0; i < permutation.size(); i++) {
		  		bitarray.add(0);
		  	}
	      
		  	// Now, that stuff is setup, all we have to do is a get_next !!!!
		 // 	System.out.println("Permutation set "+ count);
		 // 	System.out.println("Permutation "+ permutation);
		 // 	System.out.println(bitarray);
		  	
		  /*	while ((tuple1 = dp_i1.get_next()) != null) 
		  	{
		  		System.out.println(tuple1.getIntFld(join_col_in1));
		  	}
		  	
		  	while ((tuple1 = dp_i2.get_next()) != null) 
		  	{
		  		System.out.println(tuple1.getIntFld(join_col_in2));
		  	}*/
		  	
		  	
	    }

	  	@Override
	  	public Tuple get_next() throws IOException, JoinsException, IndexException, InvalidTupleSizeException,
	  		InvalidTypeException, PageNotReadException, TupleUtilsException, PredEvalException, SortException,
			LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception 
	  	{
	  		while(true)
	  		{
	  		//	Thread.sleep(100);
	  		//	System.out.println("Inner "+inner);
	  		//	System.out.println("outer " + outer);
	  			//System.out.println("perm " + permutation.size());
	  			if(outer < permutation.size())
	  			{
	  				if(flag1)
	  				{
	  					//System.out.println("Came outer");
	  					int position = permutation.get(outer);
		  				bitarray.set(position, 1);
		  				//System.out.println("bit array "+bitarray);
		  				inner = position + equalityOffset;
		  				//System.out.println("Inner 2  "+inner);
		  				flag1 = false;
	  				}
	  				if(inner < permutation.size())
	  				{
	  					//System.out.println("Came inner");
	  					if(bitarray.get(inner) == 1)
	  					{
	  						//System.out.println("came if");
	  						
	  						//System.out.println(inner+"  ddd "+ permutation.get(outer));
	  						tuple1= L1.get(inner);
	  						
	  						//System.out.println("---->get2 "+ tuple1.getIntFld(1));
	  						Tuple Rtuple = new Tuple();
	  						AttrType types[] = new AttrType[perm_mat.length];
	  						for(int i=0;i<types.length;i++)
	  						{
	  							types[i]= new AttrType(AttrType.attrInteger);
	  						}
	  					  //	AttrType types[] = {new AttrType(1), new AttrType(1), new AttrType(1), new AttrType(1)}; 
	  					  	Rtuple.setHdr((short) types.length, types, inner_str_sizes);
	  				//		Rtuple.setIntFld(1, tuple1.getIntFld(perm_mat[0].offset));
	  				//		Rtuple.setIntFld(3, tuple1.getIntFld(perm_mat[2].offset));
	  						tuple2 = L1.get(permutation.get(outer));
	  						if(tuple1.getIntFld(jc_in1) == tuple2.getIntFld(jc_in1) && tuple1.getIntFld(jc_in2) == tuple2.getIntFld(jc_in2) )
	  						{
	  							inner++;
	  							continue;
	  						}
	  					  	for(int i=0;i<perm_mat.length-2;i++)
	  					  	{
	  					  		FldSpec fld = perm_mat[i];
	  					  		if(fld.relation.key == RelSpec.outer)
	  					  		{
	  					  			Rtuple.setIntFld(i+1, tuple1.getIntFld(perm_mat[i].offset));
	  					  		}
	  					  		else
	  					  		{
	  					  			Rtuple.setIntFld(i+1, tuple2.getIntFld(perm_mat[i].offset));
	  					  		}
	  					  	}
	  					  	
	  					    Rtuple.setIntFld(perm_mat.length-1, tuple1.getIntFld(perm_mat[perm_mat.length-2].offset));
	  					    Rtuple.setIntFld(perm_mat.length, tuple2.getIntFld(perm_mat[perm_mat.length-1].offset));
	  				//		Rtuple.setIntFld(2, tuple2.getIntFld(perm_mat[1].offset));
	  				//		Rtuple.setIntFld(4, tuple2.getIntFld(perm_mat[3].offset));
	  						inner++;
	  						if(inner == permutation.size())
	  	  					{
	  	  						flag1 = true;
	  	  						outer++;
	  	  					}
	  						return Rtuple;
	  					}
	  					inner++;
	  				}
	  				if(inner == permutation.size())
  					{
  						flag1 = true;
  						outer++;
  					}
	  			}
	  			else
	  				return null;
	  		}
	  	}

	  	@Override
	  	public void close() throws IOException, JoinsException, SortException, IndexException {
	  		// TODO Auto-generated method stub
	  	}
}
