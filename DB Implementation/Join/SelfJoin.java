package iterator;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

import global.AttrType;
import global.GlobalConst;
import global.TupleOrder;
import heap.Heapfile;
import heap.Tuple;
import index.IndexException;

public class SelfJoin extends Iterator implements GlobalConst{
	private AttrType _in1[], _in2[];
	private int in1_len, in2_len;
	private Sort p_i1, // pointers to the two iterators. If the
			p_i2, iter; // inputs are sorted, then no sorting is done
	private TupleOrder _order; // The sorting order.
	private CondExpr OutputFilter[];

	private boolean get_from_in1, get_from_in2; // state variables for get_next
	private int jc_in1, jc_in2;
	private boolean process_next_block;
	private short inner_str_sizes[];
	private IoBuf io_buf1, io_buf2;
	private Tuple TempTuple1, TempTuple2;
	private Tuple tuple1, tuple2;
	private boolean done;
	private byte _bufs1[][], _bufs2[][];
	private int _n_pages;
	private Heapfile temp_file_fd1, temp_file_fd2;
	private AttrType sortFldType;
	private int t1_size, t2_size;
	private Tuple Jtuple;
	private FldSpec perm_mat[];
	private int nOutFlds;
	private Sort base1 = null;
	private int outer = 0, inner = 0;
	private ArrayList<Tuple> L1 = new ArrayList<Tuple>();
	private HashMap<Integer, Integer> hm  = new HashMap<Integer,Integer>();
	private HashMap<Integer, Integer> hm2  = new HashMap<Integer,Integer>();
	int index = 0;
	int operator = -1;
	int kj = 0;
	private int join_col_in;

	public SelfJoin(AttrType in1[], int len_in1, short s1_sizes[], AttrType in2[], int len_in2, short s2_sizes[],

			int join_col_in1, int sortFld1Len,

			int amt_of_mem, Iterator am1, Iterator am2,

			boolean in1_sorted, boolean in2_sorted, TupleOrder order,

			CondExpr outFilter[], FldSpec proj_list[], int n_out_flds) throws UnknowAttrType, LowMemException, JoinsException, Exception
	{
		_in1 = new AttrType[in1.length];
		_in2 = new AttrType[in2.length];
		System.arraycopy(in1, 0, _in1, 0, in1.length);
		System.arraycopy(in2, 0, _in2, 0, in2.length);
		in1_len = len_in1;
		in2_len = len_in2;
		join_col_in = join_col_in1;
		Jtuple = new Tuple();
		AttrType[] Jtypes = new AttrType[n_out_flds];
		short[] ts_size = null;
		perm_mat = proj_list;
		nOutFlds = n_out_flds;
		operator = outFilter[0].op.attrOperator;
		try {
			ts_size = TupleUtils.setup_op_tuple(Jtuple, Jtypes, in1, len_in1, in2, len_in2, s1_sizes, s2_sizes,
					proj_list, n_out_flds);
		} catch (Exception e) {
			throw new TupleUtilsException(e, "Exception is caught by SortMerge.java");
		}

		int n_strs2 = 0;

		for (int i = 0; i < len_in2; i++)
			if (_in2[i].attrType == AttrType.attrString)
				n_strs2++;
		inner_str_sizes = new short[n_strs2];

		for (int i = 0; i < n_strs2; i++)
			inner_str_sizes[i] = s2_sizes[i];

		p_i1 = null;
		p_i2 = null;
		
		if (!in1_sorted) {
			try 
			{
				p_i1 = new Sort(in1, (short) len_in1, s1_sizes, am1, join_col_in1, order, sortFld1Len, amt_of_mem / 2);
			} 
			catch (Exception e) 
			{
				throw new SortException(e, "Sort failed");
			}
		}
		base1 = new Sort(p_i1);
		Tuple tupletmp = new Tuple();
		int in = 0;
		while ((tupletmp = p_i1.get_next())!=null)
		{
			hm.put(tupletmp.getIntFld(join_col_in1), in);
			if(hm2.get(tupletmp.getIntFld(join_col_in1)) == null)
			{
				hm2.put(tupletmp.getIntFld(join_col_in1), in);
	//			System.out.println(tupletmp.getIntFld(3)+"  "+in);
			}
			in++;
			L1.add(new Tuple(tupletmp));
		}
		
	/*	for(int i=0;i<L1.size();i++)
		{
			System.out.println(L1.get(i).getIntFld(3));
		}*/
		OutputFilter = outFilter;
		_order = order;
		jc_in1 = join_col_in1;
	//	jc_in2 = join_col_in2;
		get_from_in1 = true;
		get_from_in2 = true;

		// open io_bufs
		io_buf1 = new IoBuf();
		io_buf2 = new IoBuf();

		// Allocate memory for the temporary tuples
		TempTuple1 = new Tuple();
		TempTuple2 = new Tuple();
		tuple1 = new Tuple();
		tuple2 = new Tuple();

		if (io_buf1 == null || io_buf2 == null || TempTuple1 == null || TempTuple2 == null || tuple1 == null
				|| tuple2 == null)
			throw new JoinNewFailed("SortMerge.java: allocate failed");
		if (amt_of_mem < 2)
			throw new JoinLowMemory("SortMerge.java: memory not enough");

		try {
			TempTuple1.setHdr((short) in1_len, _in1, s1_sizes);
			tuple1.setHdr((short) in1_len, _in1, s1_sizes);
			TempTuple2.setHdr((short) in2_len, _in2, s2_sizes);
			tuple2.setHdr((short) in2_len, _in2, s2_sizes);
		} catch (Exception e) {
			throw new SortException(e, "Set header failed");
		}
		t1_size = tuple1.size();
		t2_size = tuple2.size();

		process_next_block = true;
		done = false;

		// Two buffer pages to store equivalence classes
		// NOTE -- THESE PAGES ARE NOT OBTAINED FROM THE BUFFER POOL
		// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
		_n_pages = 1;
		_bufs1 = new byte[_n_pages][MINIBASE_PAGESIZE];
		_bufs2 = new byte[_n_pages][MINIBASE_PAGESIZE];

		temp_file_fd1 = null;
		temp_file_fd2 = null;
		try {
			temp_file_fd1 = new Heapfile(null);
			temp_file_fd2 = new Heapfile(null);

		} catch (Exception e) {
			throw new SortException(e, "Create heap file failed");
		}

		sortFldType = _in1[jc_in1 - 1];
	}

	public Tuple get_next() throws SortException, UnknowAttrType, LowMemException, JoinsException, IOException, Exception 
	{
		while(outer < L1.size())
		{
			//System.out.println("outer "+outer+" inner "+inner);
			//System.out.println(tuple1.getIntFld(1));
			if(OutputFilter[0].op.attrOperator == 1 || OutputFilter[0].op.attrOperator == 2)
			{
				index = hm2.get(L1.get(outer).getIntFld(join_col_in))-1;
			}
			else
			{
				index = hm.get(L1.get(outer).getIntFld(join_col_in));
			}
		//	System.out.println("index "+index);
			if(index < 0)
			{
				outer++;
				continue;
			}
			if(inner<=index)
			{
				TempTuple1 = L1.get(outer);
				TempTuple2 = L1.get(inner);
				Tuple Rtuple = new Tuple();
				AttrType types[] = {new AttrType(1), new AttrType(1)}; 
				Rtuple.setHdr((short) 2, types, inner_str_sizes);
				Rtuple.setIntFld(1, TempTuple1.getIntFld(perm_mat[0].offset));
				Rtuple.setIntFld(2, TempTuple2.getIntFld(perm_mat[0].offset));
				inner++;
				return Rtuple;
			}
			else
			{
				outer++;
				inner = 0; // Check
			}
		}
		return null;
	}

	@Override
	public void close() throws IOException, JoinsException, SortException, IndexException {
		// TODO Auto-generated method stub
		
	}

}
