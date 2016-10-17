package tests;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import bufmgr.PageNotReadException;
import global.AttrOperator;
import global.AttrType;
import global.GlobalConst;
import global.RID;
import global.SystemDefs;
import global.TupleOrder;
import heap.FieldNumberOutOfBoundException;
import heap.FileAlreadyDeletedException;
import heap.HFBufMgrException;
import heap.HFDiskMgrException;
import heap.HFException;
import heap.Heapfile;
import heap.InvalidSlotNumberException;
import heap.InvalidTupleSizeException;
import heap.InvalidTypeException;
import heap.Tuple;
import index.IndexException;
import iterator.CondExpr;
import iterator.FileScan;
import iterator.FldSpec;
import iterator.Iterator;
import iterator.JoinForManyPredicates;
import iterator.JoinsException;
import iterator.LightningInequalitySelfJoin;
import iterator.LowMemException;
import iterator.PredEvalException;
import iterator.RelSpec;
import iterator.SortException;
import iterator.SortMerge;
import iterator.TupleUtilsException;
import iterator.UnknowAttrType;
import iterator.UnknownKeyTypeException;
import iterator.WrongPermat;

public class JoinOptimizationTest 
{
	// Sample files
	static FileVariable R1 = new FileVariable();
	static FileVariable S1 = new FileVariable();
	static FileVariable T1 = new FileVariable();
	static FileVariable V1 = new FileVariable();
	static FileVariable W1 = new FileVariable();
	
	// Original files
	static FileVariable R, S, T, V, W;

	// Number of samples
	static final int limit = 100;
	
	static LinkedHashMap<String,ArrayList<String>> columns = new LinkedHashMap<String,ArrayList<String>>(); 
	// Predicates and Predicate Pairs
	static class Predicate 
	{
		String table1;
		String column1;
		String table2;
		String column2;
		int operation;
		Predicate(String table1, String column1, String table2, String column2, int operation)
		{
			this.table1 = table1;
			this.column1 = column1;
			this.table2 = table2;
			this.column2 = column2;
			this.operation = operation;
		}
		public Predicate() {
			// TODO Auto-generated constructor stub
		}
	}
	static class PredicatePair 
	{
		Predicate p1;
		Predicate p2;
		int change = -1;
		PredicatePair(Predicate p1, Predicate p2)
		{
			this.p1 = p1;
			this.p2 = p2;
		}
		public PredicatePair() {
			// TODO Auto-generated constructor stub
		}
	}
	
	static class Intermediates
	{
		String table1;
		String table2;
		String intermediateName;
		ArrayList<String> tablesJoined;
		FileVariable file;
		PredicatePair predPair;
		Intermediates()
		{
			
		}
		Intermediates(String t1, String t2, String name)
		{
			this.table1 = t1;
			this.table2 = t2;
			this.intermediateName = name;
		}
	}
	
	// Selection and Condition Predicates
	static class SelectCondition
	{
		CondExpr[] outFilter;
		FldSpec[] proj;
		public SelectCondition(CondExpr[] outFilter2, FldSpec[] proj1) 
		{
			this.outFilter = outFilter2;
			this.proj = proj1;
		}
	}
	
	static class QueryDetails
	{
		ArrayList<String> Ordering;
		ArrayList<PredicatePair> Predicates; 
		ArrayList<LinkedHashMap<String, Integer>> Mapping;
		
		public QueryDetails(ArrayList<String> columnorder, ArrayList<PredicatePair> predicates2,
				ArrayList<LinkedHashMap<String, Integer>> rearrangecolumn) 
		{
			this.Ordering = columnorder;
			this.Predicates = predicates2;
			this.Mapping = rearrangecolumn;
		}
	}
	// File Variable class which has all the file variables necessary
	static class FileVariable
	{
		public Heapfile hf;
		public String FileName;
		public AttrType[] Rtypes;
		public short[] Rsizes;
		int cardinality;
		public Heapfile hf1 = null;
		
		FileVariable()
		{
			
		}
		
		FileVariable(Heapfile hf, String fn, AttrType[] Rtypes, short[] Rsizes)
		{
			this.hf = hf;
			this.FileName = fn;
			this.Rtypes = Rtypes;
			this.Rsizes = Rsizes;
		}
		
		FileVariable(Heapfile hf, String fn, AttrType[] Rtypes, short[] Rsizes, int cardinality)
		{
			this.hf = hf;
			this.FileName = fn;
			this.Rtypes = Rtypes;
			this.Rsizes = Rsizes;
			this.cardinality = cardinality;
		}
		
		FileVariable(Heapfile hf, Heapfile hf1, String fn, AttrType[] Rtypes, short[] Rsizes)
		{
			this.hf = hf;
			this.hf1 = hf1;
			this.FileName = fn;
			this.Rtypes = Rtypes;
			this.Rsizes = Rsizes;
		}
		
		
		void deleteFile() throws InvalidSlotNumberException, FileAlreadyDeletedException, InvalidTupleSizeException, HFBufMgrException, HFDiskMgrException, IOException
		{
			hf.deleteFile();
			if(hf1 != null)
			{
				hf1.deleteFile();
			}
			// FileName = null;
			// this.Rtypes = null;
			// this.Rsizes = null;
		}
		iterator.Iterator getIterator()
		{
			// Create a file scan iterator of R relation
			FldSpec[] Sprojection = new FldSpec[Rtypes.length];
			for (int i = 0; i < Rtypes.length; i++) 
			{
				Sprojection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);
			}
			FileScan am = null;
			try 
			{
				am = new FileScan(FileName, Rtypes, Rsizes, (short) Rtypes.length, (short) Rtypes.length, Sprojection, null);
			}
			catch (Exception e) 
			{
				System.err.println("" + e);
			}
			return am;	
		}
		
	}
	
	// Do a heap scan on the passed file (as a string)
	private static void heapScan(String f, AttrType[] types, short[] Ssizes) throws JoinsException,
			PageNotReadException, PredEvalException, UnknowAttrType, FieldNumberOutOfBoundException, WrongPermat
	{
		FldSpec[] Sprojection = new FldSpec[types.length];
		for (int i = 0; i < types.length; i++) 
		{
			Sprojection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);
		}
		FileScan am = null;
		try 
		{
			am = new FileScan(f, types, Ssizes, (short) types.length, (short) types.length, Sprojection, null);
		}
		catch (Exception e) {
			System.err.println("" + e);
		}
		// System.out.println("Stypes.lenght"+Stypes.length);
		Tuple t = new Tuple();
		try {
			t.setHdr((short) types.length, types, Ssizes);
			t = am.get_next();
			while (t != null) {
				for(int i=0;i<types.length;i++)
				{
					System.out.println(t.getIntFld(i+1));
				}
				t = am.get_next();
				System.out.println("---xx");
			}
		} catch (InvalidTypeException e) {
			e.printStackTrace();
		} catch (InvalidTupleSizeException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	// Create the system definition
	private static void createDB() 
	{
		String dbpath = "/tmp/" + System.getProperty("user.name") + ".minibase.jointestdb";
		String logpath = "/tmp/" + System.getProperty("user.name") + ".joinlog";

		String remove_cmd = "/bin/rm -rf ";
		String remove_logcmd = remove_cmd + logpath;
		String remove_dbcmd = remove_cmd + dbpath;
		String remove_joincmd = remove_cmd + dbpath;

		try 
		{
			Runtime.getRuntime().exec(remove_logcmd);
			Runtime.getRuntime().exec(remove_dbcmd);
			Runtime.getRuntime().exec(remove_joincmd);
		} 
		catch (IOException e)
		{
			System.err.println("" + e);
		}

		SystemDefs sysdef = new SystemDefs(dbpath, 1000000, 500000, "Clock");

		// Initialize the tables
		
		ArrayList<String> temp;
		temp = new ArrayList<String>(Arrays.asList("id","dept","salary","tax"));
		columns.put("r", temp);
		temp = new ArrayList<String>(Arrays.asList("id","dept","salary","tax","id2","start","end"));
		columns.put("s", temp);
		temp = new ArrayList<String>(Arrays.asList("id2","start","end","id","dept","salary","tax"));
		columns.put("t", temp);
		temp = new ArrayList<String>(Arrays.asList("id","dept","salary","tax","id2","start","end"));
		columns.put("v", temp);
		temp = new ArrayList<String>(Arrays.asList("id2","start","end"));
		columns.put("w", temp);
	}
	
	public static HashMap<Integer,Integer> Black_Box_u2(int N, int r)
	{

		HashMap<Integer,Integer> map = new HashMap<Integer,Integer>();
		Set<Integer> set = new HashSet<Integer>();
		int A[] = new int[r];
		
		
		int n = 0;
		
		for( int i=0; i<N; i++)
		{
			n = n+1;
			
			double d = ((double)1/(double)(n));
			for(int j=0; j<r; j++)
			{
				
				if( Math.random() <= d )
				{	
					if(set.contains(i) == false)
					{
						set.add(i);
						A[j] = i;
						break;
					}
				}
			}
			
		}
		
		Set<Integer> set1 = new HashSet<Integer>();
		for(int i=0; i<r; i++)
		{
			set1.add(A[i]);
		}
		
		for(int i=0; i<r; i++)
		{
			if(set1.size() < r)
			{
				if(!set1.contains((n/2) + i))
				{
					set1.add((n/2) + i);
					map.put((n/2) + i, 1);
				}
			}
		}
		
		for(int i=0; i<r; i++)
			map.put(A[i], 1);
		
		
		return map;
		
	}
	
	public static HashMap<Integer, Integer> Black_Box_WR2(int N, int r)
	{
		HashMap<Integer,Integer> map = new HashMap<Integer,Integer>();
		int A[] = new int[r];
		
		
		int CummulativeWeight = 0;
		
		for( int i=0; i<N; i++)
		{
			int weight = N*(N+1)/2;
			CummulativeWeight += weight;
			double d = ((double)weight/(double)(CummulativeWeight));
			for(int j=0; j<r; j++)
			{
				
				if( Math.random() <= d)
				{	
					A[j] = i;
					break;
				}
			}
			
		}
		Set<Integer> set1 = new HashSet<Integer>();
		for(int i=0; i<r; i++)
		{
			set1.add(A[i]);
		}
		
		for(int i=0; i<r; i++)
		{
			if(set1.size() < r)
			{
				if(!set1.contains((N/2) + i))
				{
					set1.add((N/2) + i);
					map.put((N/2) + i, 1);
				}
			}
		}
		
		for(int i =0; i< r; i++)
		{
			map.put(A[i], 1);
		}
		return map;
		
	}
	

	public static HashMap<Integer, Integer> unweightedWRSampling_firstTen( int n, int r )
	{
		HashMap<Integer, Integer> output = new HashMap<Integer, Integer>();
		
		int x = r, i =0;
		
		while( i < n && (x > 0))
		{
			output.put(i,1);
			x--;
			i++;
		}
		
		return output;
		
	}
	
	public static HashMap<Integer, Integer> unweightedWRSampling_lastTen( int n, int r )
	{
		HashMap<Integer, Integer> output = new HashMap<Integer, Integer>();
		
		int x = r, i =n;
		
		while( i > 0 && (x > 0))
		{
			output.put(i,1);
			x--;
			i--;
		}
		
		return output;
		
	}
	
	public static HashMap<Integer, Integer> unweightedWRSampling_Random( int n, int r)
	{
		HashMap<Integer, Integer> output = new HashMap<Integer, Integer>();
	   int counter = 0;
	   while( counter < r )
	   {
		   double random = Math.random();
		   if(output.get( (int) (n * random)) == null)
		   {
			   output.put( (int) (n * random) , 1);
			   counter++;
		   }
	   }
	return output;
	   
	
		
	}	
	
	public static HashMap<Integer, Integer> stratifiedSampling(int n, int r)
	{
		HashMap<Integer, Integer> output = new HashMap<Integer, Integer>();
		
		for(int i=1; i<=r; i++)
		{
			int low = (i-1)*n/r +1;
			int high = i*n/r;
			
			int t = (int)(Math.random() * (double)(high - low) + (i-1)*( high-low ));
			//System.out.println("High " + high + " Low " + low + " T "+t);
			output.put(t, 1);
		}
		return output;
	}
	
	private static AttrType[] returnTypes(ArrayList<Integer> ordering)
	{
		AttrType[] rTypes = new AttrType[ordering.size()];
		for (int i = 0; i < ordering.size(); i++) 
		{
			rTypes[i] = new AttrType(AttrType.attrInteger);
		}
		return rTypes;
	}
	
	// Given a file name, build the file variable with only the columns in the predicate
	public static FileVariable getHeapFile(String file, ArrayList<Integer> ordering) throws HFException, HFBufMgrException, HFDiskMgrException, IOException
	{
		FileVariable FileSample = new FileVariable();
		FileVariable fv = new FileVariable();
		String[] fileName = file.split("[.]");
		String fileN = fileName[0]+".in";
		String fileSampleN = fileName[0]+"sample.in";
	//	System.out.println(fileN);
		Heapfile fr = new Heapfile(fileN);
		Heapfile frs = new Heapfile(fileSampleN);
		AttrType[] Types = returnTypes(ordering);
		short[] Rsizes = new short[0];
		HashMap<Integer,Integer> randomNumbers = doRandomSampling(limit,countLines(new File("/home/osboxes/Downloads/minjava/"+file)));
		try 
		{
			BufferedReader br = new BufferedReader(new FileReader(new File(file)));
			int count = 0;
			int size = 0;
			RID rid;
			Tuple t = new Tuple();
			t = new Tuple();
			t.setHdr((short) Types.length, Types, Rsizes);
			size = t.size();
			t = new Tuple(size);
			t.setHdr((short) Types.length, Types, Rsizes);
			for (String line; (line = br.readLine()) != null;)
			{
				String str[] = line.split(",");
				int tuplePos = 0;
				for(int i=0;i<ordering.size();i++)
				{
					int flag = 0;
					for (int j = 0; j < str.length; j++)
					{
						if(ordering.get(i) == j+1)
						{
							t.setIntFld(tuplePos + 1, Integer.parseInt(str[j]));
						//	System.out.println(t.getIntFld(tuplePos+1));
							tuplePos++;
							flag = 1;
						}
					}
					if(flag == 0)
					{
						t.setIntFld(tuplePos + 1, 0);
						tuplePos++;
					}
				}
				rid = fr.insertRecord(t.returnTupleByteArray());
				if(randomNumbers.get(count)!=null)
				{
					//System.out.println(count);
					rid = frs.insertRecord(t.returnTupleByteArray());
				}
				count++;
			}			
			fv.hf = fr;
			fv.Rsizes = Rsizes;
			fv.Rtypes = Types;
			fv.FileName = fileN;
			
			// Populate Sample Child
			FileSample.hf = frs;
			FileSample.Rsizes = Rsizes;
			FileSample.Rtypes = Types;
			FileSample.FileName = fileSampleN;
			
			switch(file)
			{
				case "F1.txt":
					R1 = FileSample;
					break;
				case "F2.txt":
					S1 = FileSample;
					break;
				case "F3.txt":
					T1 = FileSample;
					break;
				case "F4.txt":
					V1 = FileSample;
					break;
				case "F5.txt":
					W1 = FileSample;
					break;
			}
		}
		catch (Exception e)
		{
			e.printStackTrace();
		}
		return fv;
	}
	
	// Iterate over a given File Variable
	private static void iterate(FileVariable F) throws JoinsException, IndexException, PageNotReadException, TupleUtilsException, PredEvalException, SortException, LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception
	{
		System.out.println("Iterating "+F.FileName);
		Tuple t = new Tuple();
		try 
		{
			t.setHdr((short) F.Rtypes.length, F.Rtypes, F.Rsizes);
			iterator.Iterator am = F.getIterator();
			t = am.get_next();
			while (t != null) 
			{
				for(int i=0;i<F.Rtypes.length;i++)
				{
					System.out.print(t.getIntFld(i+1));
					if(i+1 < F.Rtypes.length)
						System.out.print(" x ");
				}
				System.out.println();
				t = am.get_next();
			}
		} 
		catch (InvalidTypeException e) 
		{
			e.printStackTrace();
		}
		catch (InvalidTupleSizeException e)
		{
			e.printStackTrace();
		}
		catch (IOException e)
		{
			e.printStackTrace();
		}
	}
	
	//Get the ordering in numbers
	private static ArrayList<Integer> getOrdering(ArrayList<String> ordering, HashMap<String, Integer> mapping) 
	{
		ArrayList<Integer> nOrdering = new ArrayList<Integer>();
		for(int i=0;i<ordering.size();i++)
		{
			if(mapping.get(ordering.get(i)) == null)
			{
				nOrdering.add(0);
			}
			else
			{
				nOrdering.add(mapping.get(ordering.get(i)));
			}
		}
		/*for(int i=0;i<nOrdering.size();i++)
		{
			System.out.println(nOrdering.get(i));
		}*/
		return nOrdering;
	}
	
	// Return the cardinality
	private static int joinCardinality(CondExpr[] outFilter, FldSpec[] proj, FileVariable R, FileVariable S) throws JoinsException, IndexException, PageNotReadException, TupleUtilsException, PredEvalException, SortException, LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception 
	{
		FileVariable combinedFile = combineFiles(R,S);
		AttrType[] RTypes = combinedFile.Rtypes;
		AttrType[] STypes = combinedFile.Rtypes;
		short[] Rsizes = combinedFile.Rsizes;
		short[] Ssizes = combinedFile.Rsizes;
		FldSpec[] proj1 = new FldSpec[proj.length+2];
		for(int i=0;i<proj.length;i++)
		{
			proj1[i] = proj[i];
		}
		proj1[proj.length] = new FldSpec(new RelSpec(RelSpec.outer), RTypes.length);
		proj1[proj.length+1] = new FldSpec(new RelSpec(RelSpec.outer), RTypes.length);
		iterator.Iterator am1 = combinedFile.getIterator();
		iterator.Iterator am2 = combinedFile.getIterator();
	//	iterate(combinedFile);
		int car = 0;
		JoinForManyPredicates lj = null;
		TupleOrder ascending = new TupleOrder(TupleOrder.Ascending);
		TupleOrder descending = new TupleOrder(TupleOrder.Descending);
		long start = System.currentTimeMillis();
		long freemem = Runtime.getRuntime().freeMemory();
		try 
		{
			if(outFilter[0].op.attrOperator == 2 || outFilter[0].op.attrOperator == 5)
			{
				if(outFilter[1].op.attrOperator == 2 || outFilter[1].op.attrOperator == 5)
				{
					lj = new JoinForManyPredicates(RTypes, RTypes.length, Rsizes, STypes, STypes.length, Ssizes, 
							outFilter[0].operand1.symbol.offset, 4, outFilter[1].operand1.symbol.offset, 4, 
							50, am1, am2, false, false, ascending, descending, outFilter, proj1, proj1.length);
				}
				else
				{
					lj = new JoinForManyPredicates(RTypes, RTypes.length, Rsizes, STypes, STypes.length, Ssizes, 
							outFilter[0].operand1.symbol.offset, 4, outFilter[1].operand1.symbol.offset, 4, 
							50, am1, am2, false, false, ascending, ascending, outFilter, proj1, proj1.length); 
				}
			}
			else
			{
				if(outFilter[1].op.attrOperator == 2 || outFilter[1].op.attrOperator == 5)
				{
					lj = new JoinForManyPredicates(RTypes,RTypes.length, Rsizes, STypes, STypes.length, Ssizes, 
							outFilter[0].operand1.symbol.offset, 4, outFilter[1].operand1.symbol.offset, 4, 
							50, am1, am2, false, false, descending ,descending, outFilter, proj1, proj1.length);
				}
				else
				{
					lj = new JoinForManyPredicates(RTypes, RTypes.length, Rsizes, STypes, STypes.length, Ssizes, 
							outFilter[0].operand1.symbol.offset, 4, outFilter[1].operand1.symbol.offset, 4, 
							50, am1, am2, false, false, descending, ascending, outFilter, proj1, proj1.length);
				}
			}
			//System.out.println("Sort iterator got in "+(System.currentTimeMillis()-start)+" mseconds");
			//System.out.println("Memory used : " + (Runtime.getRuntime().freeMemory()-freemem)/(1024*1024));
			Tuple tuple = new Tuple();
			start = System.currentTimeMillis();
			while(( tuple = lj.get_next())!=null)
			{
				if(tuple.getIntFld(proj1.length-1) == 1 && tuple.getIntFld(proj1.length) == 2)
				{
				//	System.out.println(tuple.getIntFld(1)+"x"+tuple.getIntFld(2)+"x"+tuple.getIntFld(3)+"x"+tuple.getIntFld(4));
					car++;
				}
			}
		} 
		catch (Exception e) 
		{
			System.err.println("*** join error in SortMerge constructor ***");
			System.err.println("" + e);
			e.printStackTrace();
		}
		combinedFile.deleteFile();
		return car;
	}
	
	// Return the joined file
	private static FileVariable joinFile(CondExpr[] outFilter, FldSpec[] proj, FileVariable r, FileVariable s, String joinedName, ArrayList<Integer> zeroPositions) throws JoinsException, IndexException, PageNotReadException, TupleUtilsException, PredEvalException, SortException, LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception 
	{
//		String joinedName = new String(R.FileName.split("[.]")[0] + "join"+ S.FileName.split("[.]")[0])+".in";
//		System.out.println(joinedName);
		Heapfile joinedFile = new Heapfile(joinedName);
		RID rid , rid1; 
 		AttrType[] Types = new AttrType[0];
		FileVariable combinedFile = combineFiles(r,s);
		AttrType[] RTypes = combinedFile.Rtypes;
		AttrType[] STypes = combinedFile.Rtypes;
		FldSpec[] proj1 = new FldSpec[proj.length+2];
		for(int i=0;i<proj.length;i++)
		{
			proj1[i] = proj[i];
		}
		proj1[proj.length] = new FldSpec(new RelSpec(RelSpec.outer), RTypes.length);
		proj1[proj.length+1] = new FldSpec(new RelSpec(RelSpec.outer), RTypes.length);
		short[] Rsizes = combinedFile.Rsizes;
		short[] Ssizes = combinedFile.Rsizes;
		iterator.Iterator am1 = combinedFile.getIterator();
		iterator.Iterator am2 = combinedFile.getIterator();
		//System.out.println("Combineddd");
		//iterate(combinedFile);
		System.out.println("Operator "+outFilter[0].op.attrOperator+ "  "+ outFilter[1].op.attrOperator);
		System.out.println("Join columns "+outFilter[0].operand1.symbol.offset+" "+outFilter[0].operand2.symbol.offset+" "+outFilter[1].operand1.symbol.offset+" "+outFilter[1].operand2.symbol.offset);
		int cardinality = 0;
		JoinForManyPredicates lj = null;
		TupleOrder ascending = new TupleOrder(TupleOrder.Ascending);
		TupleOrder descending = new TupleOrder(TupleOrder.Descending);
		long start = System.currentTimeMillis();
		long freemem = Runtime.getRuntime().freeMemory();
		//System.out.println(outFilter[0].operand1.symbol.offset + "  " + outFilter[1].operand1.symbol.offset);
		try 
		{
			if(outFilter[0].op.attrOperator == 2 || outFilter[0].op.attrOperator == 5)
			{
				if(outFilter[1].op.attrOperator == 2 || outFilter[1].op.attrOperator == 5)
				{
					lj = new JoinForManyPredicates(RTypes, RTypes.length, Rsizes, STypes, STypes.length, Ssizes, 
							outFilter[0].operand1.symbol.offset, 4, outFilter[1].operand1.symbol.offset, 4, 
							500, am1, am2, false, false, ascending, descending, outFilter, proj1, 2);
				}
				else
				{
					lj = new JoinForManyPredicates(RTypes, RTypes.length, Rsizes, STypes, STypes.length, Ssizes, 
							outFilter[0].operand1.symbol.offset, 4, outFilter[1].operand1.symbol.offset, 4, 
							500, am1, am2, false, false, ascending, ascending, outFilter, proj1, 2); 
				}
			}
			else
			{
				if(outFilter[1].op.attrOperator == 2 || outFilter[1].op.attrOperator == 5)
				{
					lj = new JoinForManyPredicates(RTypes,RTypes.length, Rsizes, STypes, STypes.length, Ssizes, 
							outFilter[0].operand1.symbol.offset, 4, outFilter[1].operand1.symbol.offset, 4, 
							500, am1, am2, false, false, descending ,descending, outFilter, proj1, 2);
				}
				else
				{
					lj = new JoinForManyPredicates(RTypes, RTypes.length, Rsizes, STypes, STypes.length, Ssizes, 
							outFilter[0].operand1.symbol.offset, 4, outFilter[1].operand1.symbol.offset, 4, 
							500, am1, am2, false, false, descending, ascending, outFilter, proj1, 2);
				}
			}
			//System.out.println("Sort iterator got in "+(System.currentTimeMillis()-start)+" mseconds");
			//System.out.println("Memory used : " + (Runtime.getRuntime().freeMemory()-freemem)/(1024*1024));
			Tuple tuple = new Tuple();
			
			// Create output file and tuple
			Types = new AttrType[RTypes.length+4-1]; // Hard coded
			for(int i=0;i<Types.length;i++)
			{
				Types[i] = new AttrType(AttrType.attrInteger);
			}
			
			// Tuple R
			Tuple newTupleR = new Tuple();
			newTupleR.setHdr((short) Types.length, Types, Ssizes);
			int size = newTupleR.size();
			newTupleR = new Tuple(size);
			newTupleR.setHdr((short) Types.length, Types, Ssizes);
			
			// Tuple S
		/*	Tuple newTupleS = new Tuple();
			newTupleS.setHdr((short) Types.length, Types, Ssizes);
			size = newTupleR.size();
			newTupleS = new Tuple(size);
			newTupleS.setHdr((short) Types.length, Types, Ssizes);*/
			int counterR = 0;
		//	int counterS = 0;
			//r.deleteFile();
			//s.deleteFile();
			//r.hf = new Heapfile(r.FileName);
			//s.hf = new Heapfile(s.FileName);
			String rfilename = r.FileName;
			String sfilename = s.FileName;
			int rel;
			int startPos = -1;
			if(rfilename.startsWith("intermediate"))
			{
				 rel = RelSpec.innerRel;
				 startPos = RTypes.length;
			}
			else
			{
				 rel = RelSpec.outer;
				 startPos = 1;
			}
			while(( tuple = lj.get_next())!=null)
			{
				counterR = 0;
			//	counterS = 0;
				if(tuple.getIntFld(proj1.length-1) == 1 && tuple.getIntFld(proj1.length) == 2)
				{
					for(int i=0;i<proj1.length-2;i++)
					{
						if(proj1[i].relation.key == rel)
						{
						//	System.out.println("hi"+tuple.getIntFld(i+1));
							if(zeroPositions !=null)
							{
								if(!zeroPositions.contains(i+2-startPos))
								{
									newTupleR.setIntFld(counterR+1, tuple.getIntFld(i+1));
									counterR++;
								}
							}
							else
							{
								newTupleR.setIntFld(counterR+1, tuple.getIntFld(i+1));
								counterR++;
							}
						}
						else
						{
							newTupleR.setIntFld(counterR+1, tuple.getIntFld(i+1));
							counterR++;
						}
				//		System.out.print(newTupleR.getIntFld(i+1)+" ");
						/*if(proj[i].relation.key == RelSpec.innerRel)
						{
							newTupleS.setIntFld(counterS+1, tuple.getIntFld(i+1));
							counterS++;
						}	*/
					}
				//	System.out.println();
					cardinality++;
					rid = joinedFile.insertRecord(newTupleR.returnTupleByteArray());
				//	rid1 = s.hf.insertRecord(newTupleS.returnTupleByteArray());
				}
			}
		} 
		catch (Exception e) 
		{
			System.err.println("*** join error in SortMerge constructor ***");
			System.err.println("" + e);
			e.printStackTrace();
		}
		// Build the file Variable
		FileVariable joinedFileVar = new FileVariable(joinedFile, joinedName, Types, Ssizes, cardinality);
		System.out.println("Intermediate Cardinality : "+cardinality);
		//iterate(joinedFileVar);
		combinedFile.deleteFile();
		return joinedFileVar;
	}
	
	// Combine the files into one file in order to get 2c working
	private static FileVariable combineFiles(FileVariable R, FileVariable S) throws JoinsException, IndexException, PageNotReadException, TupleUtilsException, PredEvalException, SortException, LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception
	{
		AttrType[] Stypes, Rtypes, Types;
		short[] Sizes = R.Rsizes;
		Stypes = S.Rtypes;
		Rtypes = R.Rtypes;
		RID rid;
		String combinedName = new String(R.FileName.split("[.]")[0] + "and"+ S.FileName.split("[.]")[0])+".in";
	//	System.out.println(combinedName);
		Heapfile combinedFile = new Heapfile(combinedName);
		Types = new AttrType[Stypes.length+1];
		int j;
		for(j=0;j<Stypes.length;j++)
		{
			Types[j] = Stypes[j];
		}
		Types[j] = new AttrType(AttrType.attrInteger);
	/*	if(Stypes.length > Rtypes.length)
		{
			Types = new AttrType[Stypes.length+1];
			int i;
			for(i=0;i<Stypes.length;i++)
			{
				Types[i] = Stypes[i];
			}
			Types[i] = new AttrType(AttrType.attrInteger);
		}
		else
		{
			Types = new AttrType[Rtypes.length+1];
			int i;
			for(i=0;i<Rtypes.length;i++)
			{
				Types[i] = Rtypes[i];
			}
			Types[i] = new AttrType(AttrType.attrInteger);
		}*/
		Tuple newTuple = new Tuple();
		newTuple.setHdr((short) Types.length, Types, Sizes);
		int size = newTuple.size();
		newTuple = new Tuple(size);
		newTuple.setHdr((short) Types.length, Types, Sizes);
		
		Tuple t = new Tuple();
		Tuple t1 = new Tuple();
		try 
		{
			// Iterate R - Put 1
			t.setHdr((short) R.Rtypes.length, R.Rtypes, R.Rsizes);
			iterator.Iterator am = R.getIterator();
			t = am.get_next();
			while (t != null) 
			{
				int i;
				for(i=0;i<R.Rtypes.length;i++)
				{
					newTuple.setIntFld(i+1, t.getIntFld(i+1));
				//	System.out.println(t.getIntFld(i+1));
				}
		/*		if(Rtypes.length < Stypes.length)
				{
					for(int k = Rtypes.length;k<Stypes.length;k++)
					{
						newTuple.setIntFld(i + 1, 0);
						i++;
					}
				}*/
				newTuple.setIntFld(i + 1, 1);
				rid = combinedFile.insertRecord(newTuple.returnTupleByteArray());
				t = am.get_next();
			}
			
			// Iterate S - Put 2
			t1.setHdr((short) S.Rtypes.length, S.Rtypes, S.Rsizes);
			iterator.Iterator am1 = S.getIterator();
			t1 = am1.get_next();
			while (t1 != null) 
			{
				int i;
				for(i=0;i<R.Rtypes.length;i++)
				{
					newTuple.setIntFld(i+1, t1.getIntFld(i+1));
			//		System.out.println(t1.getIntFld(i+1)+"----->");
				}
		/*		if(Rtypes.length > Stypes.length)
				{
					for(int k = Stypes.length;k<Rtypes.length;k++)
					{
						newTuple.setIntFld(i + 1, 0);
						i++;
					}
				}*/
				newTuple.setIntFld(i + 1, 2);
				rid = combinedFile.insertRecord(newTuple.returnTupleByteArray());
				t1 = am1.get_next();
			}
			
			FileVariable combinedVar = new FileVariable(combinedFile, combinedName, Types, R.Rsizes);
		//	System.out.println("inside combine");
		//	iterate(combinedVar);
			return combinedVar;
		} 
		catch (InvalidTypeException e) 
		{
			e.printStackTrace();
		}
		catch (InvalidTupleSizeException e)
		{
			e.printStackTrace();
		}
		catch (IOException e)
		{
			e.printStackTrace();
		}
		
		return null;
	}

	// Build the conditions and the selection predicates
	private static SelectCondition populateSelectCondition(PredicatePair pred, ArrayList<String> ordering, ArrayList<Integer> selectionList)
	{
		CondExpr[] outFilter = new CondExpr[2];
		for(int i=0;i<outFilter.length;i++)
		{
			outFilter[i] = new CondExpr();
		}
		
		// Get the columns of predicate 1 and 2
		int pred1col1, pred1col2, pred2col1, pred2col2;
		pred1col1 = ordering.indexOf(pred.p1.column1)+1;
		pred1col2 = ordering.indexOf(pred.p1.column2)+1;
		pred2col1 = ordering.indexOf(pred.p2.column1)+1;
		pred2col2 = ordering.indexOf(pred.p2.column2)+1;
		
	//	System.out.println(pred1col1+" "+ pred1col2 + " "+ pred2col1 + " "+pred2col2);
		
		// Populate first predicate
		outFilter[0].next = null;
		outFilter[0].op = new AttrOperator(pred.p1.operation);
		outFilter[0].type1 = new AttrType(AttrType.attrSymbol);
		outFilter[0].type2 = new AttrType(AttrType.attrSymbol);
		outFilter[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), pred1col1);
		outFilter[0].operand2.symbol = new FldSpec(new RelSpec(RelSpec.innerRel), pred1col2);
		
		outFilter[1].next = null;
		outFilter[1].op = new AttrOperator(pred.p2.operation);
		outFilter[1].type1 = new AttrType(AttrType.attrSymbol);
		outFilter[1].type2 = new AttrType(AttrType.attrSymbol);
		outFilter[1].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), pred2col1);
		outFilter[1].operand2.symbol = new FldSpec(new RelSpec(RelSpec.innerRel), pred2col2);
		
		// Populate the select clause -- Needs to be changed in the future for all cases
		ArrayList<FldSpec> p = new ArrayList<FldSpec>();
		for(int i=0;i<selectionList.size();i++)
		{
			p.add(new FldSpec(new RelSpec(RelSpec.outer), selectionList.get(i)));
		}
		for(int i=0;i<selectionList.size();i++)
		{
			p.add(new FldSpec(new RelSpec(RelSpec.innerRel),selectionList.get(i)));
		}
		FldSpec[] proj1 = new FldSpec[p.size()];
		p.toArray(proj1);
		
		SelectCondition sc = new SelectCondition(outFilter, proj1);
		return sc;
		
	}
	
	// Overload the function to support seperate projection list
	// Build the conditions and the selection predicates
		private static SelectCondition populateSelectCondition(PredicatePair pred, ArrayList<String> ordering, ArrayList<Integer> selectionList1, ArrayList<Integer> selectionList2)
		{
			CondExpr[] outFilter = new CondExpr[2];
			for(int i=0;i<outFilter.length;i++)
			{
				outFilter[i] = new CondExpr();
			}
			
			// Get the columns of predicate 1 and 2
			int pred1col1, pred1col2, pred2col1, pred2col2;
			pred1col1 = ordering.indexOf(pred.p1.column1)+1;
			pred1col2 = ordering.indexOf(pred.p1.column2)+1;
			pred2col1 = ordering.indexOf(pred.p2.column1)+1;
			pred2col2 = ordering.indexOf(pred.p2.column2)+1;
			
		//	System.out.println(pred1col1+" "+ pred1col2 + " "+ pred2col1 + " "+pred2col2);
			
			// Populate first predicate
			outFilter[0].next = null;
			outFilter[0].op = new AttrOperator(pred.p1.operation);
			outFilter[0].type1 = new AttrType(AttrType.attrSymbol);
			outFilter[0].type2 = new AttrType(AttrType.attrSymbol);
			outFilter[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), pred1col1);
			outFilter[0].operand2.symbol = new FldSpec(new RelSpec(RelSpec.innerRel), pred1col2);
			
			outFilter[1].next = null;
			outFilter[1].op = new AttrOperator(pred.p2.operation);
			outFilter[1].type1 = new AttrType(AttrType.attrSymbol);
			outFilter[1].type2 = new AttrType(AttrType.attrSymbol);
			outFilter[1].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), pred2col1);
			outFilter[1].operand2.symbol = new FldSpec(new RelSpec(RelSpec.innerRel), pred2col2);
			
			// Populate the select clause -- Needs to be changed in the future for all cases
			ArrayList<FldSpec> p = new ArrayList<FldSpec>();
			for(int i=0;i<selectionList1.size();i++)
			{
				p.add(new FldSpec(new RelSpec(RelSpec.outer), selectionList1.get(i)));
			//	System.out.println(selectionList1.get(i));
			}
			for(int i=0;i<selectionList2.size();i++)
			{
				p.add(new FldSpec(new RelSpec(RelSpec.innerRel),selectionList2.get(i)));
			//	System.out.println(selectionList2.get(i));
			}
			FldSpec[] proj1 = new FldSpec[p.size()];
			p.toArray(proj1);
			
			SelectCondition sc = new SelectCondition(outFilter, proj1);
			return sc;
			
		}
	// Get the predicate ordering. The Predicates are present in Predicates ArrayList in the given order
	private static ArrayList<Integer> getPredicateOrdering(ArrayList<PredicatePair> Predicates, ArrayList<String> ordering) throws JoinsException, IndexException, PageNotReadException, TupleUtilsException, PredEvalException, SortException, LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception
	{
		ArrayList<Integer> predOrdering = new ArrayList<Integer>(Predicates.size());
		HashMap<Integer,Integer> predCardinality = new HashMap<Integer,Integer>(Predicates.size());
		for(int i=0;i<Predicates.size();i++)
		{
			PredicatePair p = Predicates.get(i);
			Predicate p1 = p.p1;
			Predicate p2 = p.p2;
			// Populate the FldSpec and OutFilter
			FileVariable param1 = null, param2 = null;
			switch(p1.table1)
			{
				case "r":
					param1 = R1;
					break;
				case "s":
					param1 = S1;
					break;
				case "t":
					param1 = T1;
					break;
				case "v":
					param1 = V1;
					break;
				case "w":
					param1 = W1;
					break;
			}
			switch(p1.table2)
			{
				case "r":
					param2 = R1;
					break;
				case "s":
					param2 = S1;
					break;
				case "t":
					param2 = T1;
					break;
				case "v":
					param2 = V1;
					break;
				case "w":
					param2 = W1;
					break;
			}
			
			// Testing
			// param1 = R1;
			// param2 = S1;
			ArrayList<Integer> selection = new ArrayList<Integer>();
			selection.add(1);
			SelectCondition sc = populateSelectCondition(p, ordering, selection);
			int cardinality = joinCardinality(sc.outFilter, sc.proj, param1, param2);
			predCardinality.put(i, cardinality);
		}
		predCardinality = (HashMap<Integer, Integer>) sort(predCardinality);
		for(Map.Entry<Integer, Integer> entry : predCardinality.entrySet())
		{
			predOrdering.add(entry.getKey());
			System.out.println("Pred  : "+entry.getKey()+" Card : "+entry.getValue());
		}
		return predOrdering;
	}
	
	// Method to sort the map
	public static <K, V extends Comparable<? super V>> Map<K, V> sort( Map<K, V> map )
	{
		List<Map.Entry<K, V>> list = new LinkedList<Map.Entry<K, V>>( map.entrySet() );
		Collections.sort( list, new Comparator<Map.Entry<K, V>>()
		{
			public int compare( Map.Entry<K, V> o1, Map.Entry<K, V> o2 )
			{
				return (o1.getValue()).compareTo( o2.getValue() );
			}
		});
		
		Map<K, V> result = new LinkedHashMap<K, V>();
		for (Map.Entry<K, V> entry : list)
		{
			result.put( entry.getKey(), entry.getValue() );	
		}
		return result;
	}
	
	// Method to return the number of lines in the file
	public final static int countLines(File file) throws IOException 
	{
		ProcessBuilder builder = new ProcessBuilder("wc", "-l", file.getAbsolutePath());
        Process process = builder.start();
        InputStream in = process.getInputStream();
        LineNumberReader reader = new LineNumberReader(new InputStreamReader(in));
        String line = reader.readLine();
        if (line != null)
        {
            return Integer.parseInt(line.trim().split(" ")[0]);
        } 
        else 
        {
            return -1;
        }
    }
	
	// Method to return the random numbers
	public static HashMap<Integer,Integer> doRandomSampling(int N, int limit)
	{
		Random rand = new Random();
		HashMap<Integer,Integer> randMap = new HashMap<Integer,Integer>();
		for(int i=0;i<N;)
		{
			int num = rand.nextInt(limit);
			if(randMap.get(num)==null)
			{
				randMap.put(num, 1);
				i++;
			}
		//	System.out.println("Rand " + num);
		}
		return randMap;
	}
	
	// Parse the input query file
	private static QueryDetails parseQuery() throws IOException
	{
		// for gettin input line by line
				String line = null;
				// for splitting input into strings 
				String[] linearray;
				// for storing the table names
				ArrayList<String> Tables = new ArrayList<String>();
				// temporary.. to find the unique columns in that order.
				LinkedHashSet<String> columnset = new LinkedHashSet<String>();
				// ----> final output containing the columns in order
				ArrayList<String> columnorder = new ArrayList<String>();
				// final input structure 
				ArrayList<PredicatePair> predicates = new ArrayList<PredicatePair>();
				// ----> final output containing the number for each column in all the tables.
				ArrayList<LinkedHashMap<String, Integer>> rearrangecolumn = new ArrayList<LinkedHashMap<String, Integer>>();
				//  Hard coded structure of all the tables and their columns. 
				FileReader in = new FileReader("query.txt");
				BufferedReader br = new BufferedReader(in);
				if ((line = br.readLine()) != null) {
				//	System.out.println(line);
					linearray = line.split(" ");
					for (int i = 0; i < linearray.length; i++) {
						Tables.add(linearray[i]);
					}
				}
				Predicate temppred = null;
				PredicatePair predpair = null;
				if ((line = br.readLine()) != null) {
					linearray = line.split(" ");
					//System.out.println(linearray[0]);
					if (linearray[0].equals("WHERE") && linearray.length == 8) {
						temppred = new Predicate();
						predpair = new PredicatePair();
						//System.out.println(linearray[1].split("\\.").length);
						temppred.table1 = linearray[1].split("\\.")[0];
						temppred.column1 = linearray[1].split("\\.")[1];
						temppred.operation = linearray[2].equals("<") ? 1 : 2;
						temppred.table2 = linearray[3].split("\\.")[0];
						temppred.column2 = linearray[3].split("\\.")[1];
						columnset.add(temppred.column1);
						columnset.add(temppred.column2);
						predpair.p1 = temppred; 
						temppred = new Predicate();
						temppred.table1 = linearray[5].split("\\.")[0];
						temppred.column1 = linearray[5].split("\\.")[1];
						temppred.operation = linearray[6].equals("<") ? 1 : 2;
						temppred.table2 = linearray[7].split("\\.")[0];
						temppred.column2 = linearray[7].split("\\.")[1];
						columnset.add(temppred.column1);
						columnset.add(temppred.column2);
						predpair.p2 = temppred;
						predicates.add(predpair);
			//			System.out.println(predpair.p1.column1 + "  " + predpair.p1.column2 + "  "
			//					+ predpair.p2.column1 + "  " + predpair.p2.column2 + "  ");
					}
				}
				while ((line = br.readLine()) != null) {
					linearray = line.split(" ");
					if (linearray[0].equals("AND") && linearray.length == 8) {
						temppred = new Predicate();
						predpair = new PredicatePair(); 
						temppred.table1 = linearray[1].split("\\.")[0];
						temppred.column1 = linearray[1].split("\\.")[1];
						temppred.operation = linearray[2].equals("<") ? 1 : 2;
						temppred.table2 = linearray[3].split("\\.")[0];
						temppred.column2 = linearray[3].split("\\.")[1];
						columnset.add(temppred.column1);
						columnset.add(temppred.column2);
						predpair.p1 = temppred; 
						temppred = new Predicate();
						temppred.table1 = linearray[5].split("\\.")[0];
						temppred.column1 = linearray[5].split("\\.")[1];
						temppred.operation = linearray[6].equals("<") ? 1 : 2;
						temppred.table2 = linearray[7].split("\\.")[0];
						temppred.column2 = linearray[7].split("\\.")[1];
						columnset.add(temppred.column1);
						columnset.add(temppred.column2);
						predpair.p2 = temppred;
						predicates.add(predpair);
			//			System.out.println(predpair.p1.column1 + "  " + predpair.p1.column2 + "  "
			//					+ predpair.p2.column1 + "  " + predpair.p2.column2 + "  ");
					}
				}
				for(String col : columnset)
				{
			//		System.out.println(col);
					columnorder.add(col);
				}
			/*	Iterator<String> it = columnset.iterator();
				while(it.hasNext())
				{
					String col = it.next();
					System.out.println(col);
					columnorder.add(col);
				}*/
				for(Map.Entry m:columns.entrySet()) {
					String key = (String) m.getKey();
					ArrayList<String> val = (ArrayList<String>) m.getValue();
					LinkedHashMap<String, Integer> ordering = new LinkedHashMap<String, Integer>();
					int number = 1;
					for(int i = 0; i < val.size(); i++) {
						if(columnorder.contains(val.get(i))) {
							ordering.put(val.get(i), number);
						}
						number++;
					}
			//		System.out.println(key+" "+val);
					rearrangecolumn.add(ordering);
				}
		/*		HashMap<String, Integer> temphash; 
				for(int i = 0; i < rearrangecolumn.size(); i++) {
					temphash = rearrangecolumn.get(i);
					for(Map.Entry m:temphash.entrySet()) {
						System.out.println(m.getKey()+" "+m.getValue());
					}
					System.out.println("----------------------------");
				}*/
				QueryDetails qd = new QueryDetails(columnorder, predicates, rearrangecolumn);
				br.close();
				in.close();
				return qd;
	}
	
	private static void performJoin(QueryDetails qd, ArrayList<Intermediates> inter) throws JoinsException, IndexException, PageNotReadException, TupleUtilsException, PredEvalException, SortException, LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception 
	{
		int cardinality = 0;
		ArrayList<Integer> zeroPositions = null;
		for(int o=0;o<inter.size();o++)
		{
			int flag1 = 0, flag2 = 0, interTable1 = -1, interTable2 = -1;
			
			int pos1 = -1, pos2 = -1;
			int columnStart = -1;
			int needChange = -1;
			if(!inter.get(o).predPair.p1.column1.equals(inter.get(o).predPair.p1.column2))
			{
				needChange = 1;
			}
			Intermediates in = inter.get(o);
			int col1, col2;
			col1 = qd.Ordering.indexOf(in.predPair.p1.column1);
			col2 = qd.Ordering.indexOf(in.predPair.p1.column2);
			String table1 = in.table1;
			String table2 = in.table2;
			System.out.println("table 1"+table1+" table 2"+table2);
			FileVariable param1 = null, param2 = null;
			switch(table1)
			{
				case "r":
					param1 = R;
					break;
				case "s":
					param1 = S;
					break;
				case "t":
					param1 = T;
					break;
				case "v":
					param1 = V;
					break;
				case "w":
					param1 = W;
					break;
			}
			switch(table2)
			{
				case "r":
					param2 = R;
					break;
				case "s":
					param2 = S;
					break;
				case "t":
					param2 = T;
					break;
				case "v":
					param2 = V;
					break;
				case "w":
					param2 = W;
					break;
			}
			
			if(param1 == null || param2 == null)
			{
				for(int i=0;i<inter.size();i++)
				{
					if(inter.get(i).intermediateName.equals(table1))
					{
						param1 = inter.get(i).file;
						flag1 = 1;
						interTable1 = i;
					}
					if(inter.get(i).intermediateName.equals(table2))
					{
						param2 = inter.get(i).file;
						flag2 = 1;
						interTable2 = i;
					}
				}
			}
			//System.out.println("Flag 1"+flag1+" Flag 2 "+flag2+" intertable 1"+interTable1);
			if(flag1 == 0 && flag2 == 0)
			{
				if(needChange == 1)
				{
					ArrayList<Integer> swapOrder = new ArrayList<Integer>();
					int length = param1.Rtypes.length;
					for(int i=0;i<length;i++)
					{
						if(i == col1)
						{
							swapOrder.add(col2);
						}
						else if(i == col2)
						{
							swapOrder.add(col1);
						}
						else
						{
							swapOrder.add(i);
						}
					}
					reArrange(param2,swapOrder);
				}
			}
			else if (flag1 == 1) 
			{
			//	iterate(param2);
			//	System.out.println("ccccccccccccccc");
				if(needChange == 1)
				{
					ArrayList<Integer> swapOrder = new ArrayList<Integer>();
					int length = param2.Rtypes.length;
					for(int i=0;i<length;i++)
					{
						if(i == col1)
						{
							swapOrder.add(col2);
						}
						else if(i == col2)
						{
							swapOrder.add(col1);
						}
						else
						{
							swapOrder.add(i);
						}
					}
					reArrange(param2,swapOrder);
				//	iterate(param2);
				/*	if(in.predPair.p1.operation == 1)
					{
						in.predPair.p1.operation = 2;
					}
					else
					{
						in.predPair.p1.operation = 1;
					}*/
				}
				RID rid;
				zeroPositions = new ArrayList<Integer>();
				Heapfile temp = new Heapfile("temp.in");
				Tuple newTuple = new Tuple();
				Tuple t = new Tuple();
				PredicatePair currPred = inter.get(o).predPair;
				Predicate pred = currPred.p1;
				ArrayList<String> tables = inter.get(interTable1).tablesJoined;
				pos1 = tables.indexOf(pred.table1);
				try
				{
					// Iterate f
					t.setHdr((short) param2.Rtypes.length, param2.Rtypes, param2.Rsizes);
					newTuple.setHdr((short) param1.Rtypes.length, param1.Rtypes, param1.Rsizes);
					int size = newTuple.size();
					newTuple = new Tuple(size);
					newTuple.setHdr((short) param1.Rtypes.length, param1.Rtypes, param1.Rsizes);
					iterator.Iterator am = param2.getIterator();
					t = am.get_next();
					while (t != null)
					{
						int counter = 0;
						for (int k = 0; k < tables.size(); k++)
						{
							if (tables.get(k).equals(pred.table1)||tables.get(k).equals(pred.table2)) 
							{
								for (int i = 0; i < param2.Rtypes.length; i++) 
								{
									newTuple.setIntFld(counter + 1, t.getIntFld(i + 1));
								//	System.out.println(newTuple.getIntFld(counter+1));
									if(columnStart == -1)
									{
										columnStart = counter+1;
									}
									counter++;
								}
							}
							else 
							{
								for (int i = 0; i < param2.Rtypes.length; i++)
								{
									zeroPositions.add(counter + 1);
									newTuple.setIntFld(counter + 1, 0);
								//	System.out.println(newTuple.getIntFld(counter+1));
									counter++;
								}
							}
						}
						rid = temp.insertRecord(newTuple.returnTupleByteArray());
						t = am.get_next();
					}
				//	System.out.println("Zero positions " +zeroPositions);
					FileVariable tempvar = new FileVariable(temp, "temp.in", param1.Rtypes, param1.Rsizes);
					param2.deleteFile();
					param2.hf = new Heapfile(param2.FileName);
					iterator.Iterator am1 = tempvar.getIterator();
					t = am1.get_next();
					while (t != null) 
					{
						int i;
						for (i = 0; i < param1.Rtypes.length; i++)
						{
							newTuple.setIntFld(i + 1, t.getIntFld(i + 1));
						}
						rid = param2.hf.insertRecord(newTuple.returnTupleByteArray());
						t = am1.get_next();
					}
				} 
				catch (InvalidTypeException e) 
				{
					e.printStackTrace();
				} 
				catch (InvalidTupleSizeException e) 
				{
					e.printStackTrace();
				}
				catch (IOException e) 
				{
					e.printStackTrace();
				}
				param2.Rtypes = param1.Rtypes;
				temp.deleteFile();
			}
			
			else if(flag2 == 1)
			{
				if(needChange == 1)
				{
					ArrayList<Integer> swapOrder = new ArrayList<Integer>();
					int length = param1.Rtypes.length;
					for(int i=0;i<length;i++)
					{
						if(i == col1)
						{
							swapOrder.add(col2);
						}
						else if(i == col2)
						{
							swapOrder.add(col1);
						}
						else
						{
							swapOrder.add(i);
						}
					}
					reArrange(param1,swapOrder);
				//	iterate(param1);
					int temp;
					temp = inter.get(o).predPair.p2.operation;
					inter.get(o).predPair.p2.operation = inter.get(o).predPair.p1.operation;
					inter.get(o).predPair.p1.operation = temp;
				/*	if(inter.get(o).predPair.p2.operation == 1)
					{
						inter.get(o).predPair.p2.operation = 2;
					}
					else
					{
						inter.get(o).predPair.p2.operation = 1;
					}
					if(inter.get(o).predPair.p1.operation == 1)
					{
						inter.get(o).predPair.p1.operation = 2;
					}
					else
					{
						inter.get(o).predPair.p1.operation = 1;
					}*/
				}
				RID rid;
				zeroPositions = new ArrayList<Integer>();
				Heapfile temp = new Heapfile("temp.in");
				Tuple newTuple = new Tuple();
				Tuple t = new Tuple();
				PredicatePair currPred = inter.get(o).predPair;
				Predicate pred = currPred.p1;
				ArrayList<String> tables = inter.get(interTable2).tablesJoined;
				pos1 = tables.indexOf(pred.table2);
				try {
					// Iterate f
					t.setHdr((short) param1.Rtypes.length, param1.Rtypes, param1.Rsizes);
					newTuple.setHdr((short) param2.Rtypes.length, param2.Rtypes, param2.Rsizes);
					int size = newTuple.size();
					newTuple = new Tuple(size);
					newTuple.setHdr((short) param2.Rtypes.length, param2.Rtypes, param2.Rsizes);
					iterator.Iterator am = param1.getIterator();
					t = am.get_next();
					while (t != null) 
					{
						int counter = 0;
						for (int k = 0; k < tables.size(); k++) 
						{
							if (tables.get(k).equals(pred.table1)||tables.get(k).equals(pred.table2)) 
							{
								for (int i = 0; i < param1.Rtypes.length; i++) 
								{
									newTuple.setIntFld(counter + 1, t.getIntFld(i + 1));
									if(columnStart == -1)
									{
										columnStart = counter+1;
									}
									counter++;
								}
							}
							else 
							{
								int gh = 0;
								for (int i = 0; i < param1.Rtypes.length; i++) 
								{
									zeroPositions.add(counter + 1);
									newTuple.setIntFld(counter + 1, 0);
									counter++;
								}
							}
						}
						rid = temp.insertRecord(newTuple.returnTupleByteArray());
						t = am.get_next();
					}

					FileVariable tempvar = new FileVariable(temp, "temp.in", param2.Rtypes, param2.Rsizes);
					param1.deleteFile();
					param1.hf = new Heapfile(param1.FileName);
					iterator.Iterator am1 = tempvar.getIterator();
					t = am1.get_next();
				//	cardinality = 0;
					while (t != null) 
					{
						int i;
						for (i = 0; i < param2.Rtypes.length; i++) 
						{
							newTuple.setIntFld(i + 1, t.getIntFld(i + 1));
						}
						rid = param1.hf.insertRecord(newTuple.returnTupleByteArray());
					//	cardinality++;
						t = am1.get_next();
					}
				} catch (InvalidTypeException e) {
					e.printStackTrace();
				} catch (InvalidTupleSizeException e) {
					e.printStackTrace();
				} catch (IOException e) {
					e.printStackTrace();
				}
				param1.Rtypes = param2.Rtypes;
				temp.deleteFile();
			}
			//System.out.println("Param1");
			//iterate(param1);
			//System.out.println("Param2");
			//iterate(param2);
			SelectCondition cond = null;
			ArrayList<Integer> selectionList1 = new ArrayList<Integer>();
			ArrayList<Integer> selectionList2= new ArrayList<Integer>();
			if(needChange == 1)
			{
				if(flag1 == 1)
				{
					for(int i = 0;i<param1.Rtypes.length;i++)
					{
						selectionList1.add(i+1);
					}
					for(int i = 0;i<param1.Rtypes.length;i++)
					{
						if(i+1 == columnStart+col1)
						{
							selectionList2.add(columnStart+col2);
						}
						else if(i+1 == columnStart+col2)
						{
							selectionList2.add(columnStart+col1);
						}
						else
						{
							selectionList2.add(i+1);
						}
					}
				}
				else if(flag2 == 1)
				{
					for(int i = 0;i<param1.Rtypes.length;i++)
					{
						selectionList2.add(i+1);
					}
					for(int i = 0;i<param1.Rtypes.length;i++)
					{
						if(i+1 == columnStart+col1)
						{
							selectionList1.add(columnStart+col2);
						}
						else if(i+1 == columnStart+col2)
						{
							selectionList1.add(columnStart+col1);
						}
						else
						{
							selectionList1.add(i+1);
						}
					}
				}
				else
				{
					if(columnStart == -1)
						columnStart = 1;
					for(int i = 0;i<param1.Rtypes.length;i++)
					{
						selectionList1.add(i+1);
					}
					for(int i = 0;i<param1.Rtypes.length;i++)
					{
						if(i+1 == columnStart+col1)
						{
							selectionList2.add(columnStart+col2);
						}
						else if(i+1 == columnStart+col2)
						{
							selectionList2.add(columnStart+col1);
						}
						else
						{
							selectionList2.add(i+1);
						}
					}
					System.out.println("Col1 "+col1);
					System.out.println("Col2 "+col2);
					System.out.println("Column start "+columnStart);
					System.out.println(selectionList2);
				}
				cond = populateSelectCondition(inter.get(o).predPair, qd.Ordering, selectionList1, selectionList2);
			}
			else
			{
				for(int i = 0;i<param1.Rtypes.length;i++)
				{
					selectionList1.add(i+1);
				}
				cond = populateSelectCondition(inter.get(o).predPair, qd.Ordering, selectionList1);
			}
			
			cond = changeOrdering(cond, pos1);
			inter.get(o).file = joinFile(cond.outFilter, cond.proj, param1, param2, inter.get(o).intermediateName, zeroPositions);
		//	System.out.println("Cardinality :"+cardinality);
		//	System.out.println("Afterrr");
			
		//	iterate(inter.get(o).file);
		//	System.out.println("-------------------------");
		/*	System.out.println("Predicate ----");
			PredicatePair pred = qd.Predicates.get(sampleOrder.get(o));
			Predicate p1 = pred.p1;
			Predicate p2 = pred.p2;
			FileVariable param1 = null, param2 = null;
			ArrayList<Integer> selectionList = new ArrayList<Integer>(Arrays.asList(1,2,3,4));
			SelectCondition cond = populateSelectCondition(pred, qd.Ordering, selectionList);
			switch(p1.table1)
			{
				case "r":
					param1 = R;
					break;
				case "s":
					param1 = S;
					break;
				case "t":
					param1 = T;
					break;
				case "v":
					param1 = V;
					break;
				case "w":
					param1 = W;
					break;
			}
			switch(p1.table2)
			{
				case "r":
					param2 = R;
					break;
				case "s":
					param2 = S;
					break;
				case "t":
					param2 = T;
					break;
				case "v":
					param2 = V;
					break;
				case "w":
					param2 = W;
					break;
			}
			joinFile(cond.outFilter, cond.proj, param1, param2);
			iterate(param1);
			iterate(param2);*/
		}
		
	}
	
	// to change the join column appropriately
	private static SelectCondition changeOrdering(SelectCondition cond, int interTable1) 
	{
		if(interTable1 != -1)
		{
			cond.outFilter[0].operand1.symbol.offset += (4*(interTable1));
			cond.outFilter[1].operand1.symbol.offset += (4*(interTable1)); // Hard coded
		}
	//	System.out.println(cond.outFilter[0].operand1.symbol.offset + " sddss - "+cond.outFilter[1].operand1.symbol.offset);
		return cond;
	}

	public static ArrayList<Intermediates> processLeftDeep(ArrayList<Integer> sampleOrder, QueryDetails qd)
	{
		ArrayList<Intermediates> inter = new ArrayList<Intermediates>();
		PredicatePair predPair = qd.Predicates.get(sampleOrder.get(0));
		ArrayList<PredicatePair> toProcess = new ArrayList<PredicatePair>();
		int intermediateCount = 0;
		Predicate p1 = predPair.p1;
		int i =0;
		
			Intermediates in = new Intermediates(p1.table1,p1.table2,"intermediate"+ intermediateCount++);
			in.tablesJoined = new ArrayList<String>(Arrays.asList(p1.table1,p1.table2));
			in.predPair = predPair;
			inter.add(in);
		
		
			for(i=1;i<sampleOrder.size();i++)
			{
				String table1 = "";
				ArrayList<String> t1 = null;
				predPair = qd.Predicates.get(sampleOrder.get(i));
				p1 = predPair.p1;
				for(int j=0;j<inter.size();j++)
				{
					t1 = null;
//					System.out.println("T1 : "+inter.get(j).table1);
//					System.out.println("T2 : "+inter.get(j).table2);
//					System.out.println("Name : "+inter.get(j).intermediateName);
//					System.out.println(inter.get(j).tablesJoined);
//					System.out.println("----------------");
					if(inter.get(j).tablesJoined.contains(p1.table1))
					{
						table1 = inter.get(j).intermediateName;
						t1 = new ArrayList<String>(inter.get(j).tablesJoined);
					}
				}
				
 				if(table1.equals(""))
 				{
 					//System.out.println(table1);
 					toProcess.add(predPair);
 					continue;
 				}
 				
				if(t1 !=null)
				{
					if(in.tablesJoined.contains(p1.table2))
					{
						in = new Intermediates(p1.table1,table1,"intermediate"+ intermediateCount++);
						in.tablesJoined = new ArrayList<String>();
						in.tablesJoined.add(p1.table1);
						in.tablesJoined.addAll(t1);
					}
					else
					{
						in = new Intermediates(table1,p1.table2,"intermediate"+ intermediateCount++);
						in.tablesJoined = new ArrayList<String>();
						in.tablesJoined.addAll(t1);
						in.tablesJoined.add(p1.table2);
					}
				}
				in.predPair = predPair;
				inter.add(in);
			}
			for(int k = 0;k<toProcess.size();k++)
			{
				System.out.println(toProcess.get(k).p1.table1);
			}
			while(toProcess.size() > 0)
			{
				String table1 = "";
				ArrayList<String> t1 = null;
				predPair = toProcess.get(0);
				p1 = predPair.p1;
				for(int j=0;j<inter.size();j++)
				{
			/*		System.out.println("T1 : "+inter.get(j).table1);
					System.out.println("T2 : "+inter.get(j).table2);
					System.out.println("Name : "+inter.get(j).intermediateName);
					System.out.println(inter.get(j).tablesJoined);
					System.out.println("----------------");*/
					if(inter.get(j).tablesJoined.contains(p1.table1) || inter.get(j).tablesJoined.contains(p1.table2))
					{
						table1 = inter.get(j).intermediateName;
						t1 = new ArrayList<String>(inter.get(j).tablesJoined);
					}
				}
				System.out.println("table1 " +table1);
 				if(table1.equals(""))
 				{
 					toProcess.remove(predPair);
 					toProcess.add(predPair);
 					continue;
 				}
 				
				if(t1 !=null)
				{
					if(in.tablesJoined.contains(p1.table2))
					{
						in = new Intermediates(p1.table1,table1,"intermediate"+ intermediateCount++);
						in.tablesJoined = new ArrayList<String>();
						in.tablesJoined.add(p1.table1);
						in.tablesJoined.addAll(t1);
					}
					else
					{
						in = new Intermediates(table1,p1.table2,"intermediate"+ intermediateCount++);
						in.tablesJoined = new ArrayList<String>();
						in.tablesJoined.addAll(t1);
						in.tablesJoined.add(p1.table2);
					}
				}
				in.predPair = predPair;
				inter.add(in);
				toProcess.remove(predPair);
			}
		
		for(int j=0;j<inter.size();j++)
		{
			in = inter.get(j);
			System.out.println("T1 : "+in.table1);
			System.out.println("T2 : "+in.table2);
			System.out.println("Name : "+in.intermediateName);
			System.out.println(in.tablesJoined);
		}
		return inter;
	}
	
	// Method to determine the algorithm
	public static ArrayList<Intermediates> processAlgo(ArrayList<Integer> sampleOrder, QueryDetails qd)
	{
		ArrayList<Intermediates> inter = new ArrayList<Intermediates>();
		for(int i=0;i<sampleOrder.size();i++)
		{
			PredicatePair predPair = qd.Predicates.get(sampleOrder.get(i));
			Predicate p1 = predPair.p1;
			if(inter.size() == 0)
			{
				Intermediates in = new Intermediates(p1.table1,p1.table2,"intermediate"+ i);
				in.tablesJoined = new ArrayList<String>(Arrays.asList(p1.table1,p1.table2));
				in.predPair = predPair;
				inter.add(in);
			}
			else
			{
				String table1 = "";
				ArrayList<String> t1 = null;
				String table2 = "";
				ArrayList<String> t2 = null;
 				for(int j=0;j<inter.size();j++)
				{
 			//		System.out.println(" ---> "+inter.get(j).tablesJoined);
					if(inter.get(j).tablesJoined.contains(p1.table1))
					{
						table1 = inter.get(j).intermediateName;
						t1 = new ArrayList<String>(inter.get(j).tablesJoined);
					}
					if(inter.get(j).tablesJoined.contains(p1.table2))
					{
						table2 = inter.get(j).intermediateName;
						t2 = new ArrayList<String>(inter.get(j).tablesJoined);
					}
				}
 				
 				if(table1.equals(""))
 				{
 					table1 = p1.table1;
 				}
 				if(table2.equals(""))
 				{
 					table2 = p1.table2;
 				}
 				Intermediates in = new Intermediates(table1,table2,"intermediate"+ i);
				in.tablesJoined = new ArrayList<String>();
				if(t1 !=null)
				{
					in.tablesJoined.addAll(t1);
				}
				else
				{
					in.tablesJoined.add(table1);
				}
				if(t2 != null)
				{
					in.tablesJoined.addAll(t2);
				}
				else
				{
					in.tablesJoined.add(table2);
				}
				in.predPair = predPair;
				inter.add(in);
			}
		}
/*		for(int j=0;j<inter.size();j++)
		{
			Intermediates in = inter.get(j);
			System.out.println("T1 : "+in.table1);
			System.out.println("T2 : "+in.table2);
			System.out.println("Name : "+in.intermediateName);
			System.out.println(in.tablesJoined);
		}*/
		return inter;
	}
	
	public static void reArrange(FileVariable f, ArrayList<Integer> ordering) throws JoinsException, IndexException, PageNotReadException, TupleUtilsException, PredEvalException, SortException, LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception
	{
		RID rid;
		Heapfile temp = new Heapfile("temp.in");
		Tuple newTuple = new Tuple();
		Tuple t = new Tuple();
		try 
		{
			// Iterate f 
			t.setHdr((short) f.Rtypes.length, f.Rtypes, f.Rsizes);
			newTuple.setHdr((short) f.Rtypes.length, f.Rtypes, f.Rsizes);
			int size = newTuple.size();
			newTuple = new Tuple(size);
			newTuple.setHdr((short) f.Rtypes.length, f.Rtypes, f.Rsizes);
			iterator.Iterator am = f.getIterator();
			t = am.get_next();
			while (t != null) 
			{
				int i;
				for(i=0;i<ordering.size();i++)
				{
					newTuple.setIntFld(i+1, t.getIntFld(ordering.get(i)+1));
				}
				rid = temp.insertRecord(newTuple.returnTupleByteArray());
				t = am.get_next();
			}
			
			FileVariable tempvar = new FileVariable(temp, "temp.in",f.Rtypes,f.Rsizes);
			f.deleteFile();
			f.hf = new Heapfile(f.FileName);
			iterator.Iterator am1 = tempvar.getIterator();
			t = am1.get_next();
			while (t != null) 
			{
				int i;
				for(i=0;i<f.Rtypes.length;i++)
				{
					newTuple.setIntFld(i+1, t.getIntFld(i+1));
				}
				rid = f.hf.insertRecord(newTuple.returnTupleByteArray());
				t = am1.get_next();
			}
		} 
		catch (InvalidTypeException e) 
		{
			e.printStackTrace();
		}
		catch (InvalidTupleSizeException e)
		{
			e.printStackTrace();
		}
		catch (IOException e)
		{
			e.printStackTrace();
		} 
		temp.deleteFile();
	}
	
	public static void main(String args[]) throws IndexException, TupleUtilsException, SortException, LowMemException, UnknownKeyTypeException, Exception
	{
	
		QueryDetails qd;
		try 
		{
			// Create the Database and create the table structure
			createDB();
			
			// Parse the query 
			qd = parseQuery();
			
			// Generate the heap files and sample files of all five relations 
			R = getHeapFile("F1.txt", getOrdering(qd.Ordering, qd.Mapping.get(0)));
			S = getHeapFile("F2.txt", getOrdering(qd.Ordering, qd.Mapping.get(1)));
			T = getHeapFile("F3.txt", getOrdering(qd.Ordering, qd.Mapping.get(2)));
			V = getHeapFile("F4.txt", getOrdering(qd.Ordering, qd.Mapping.get(3)));
			W = getHeapFile("F5.txt", getOrdering(qd.Ordering, qd.Mapping.get(4)));
			
			// Iterating everything
		//	iterate(R);
	//		System.out.println("-----------------------");
	//		iterate(R1);
	//		System.out.println("-----------------------");
		//	iterate(S);
	//		System.out.println("-----------------------");
			
	
						
			
		//	joinFile()
		/*	iterate(S1);
			System.out.println("-----------------------");
	//		iterate(T);
			System.out.println("-----------------------");
			iterate(T1);
			System.out.println("-----------------------");
	//		iterate(V);
			System.out.println("-----------------------");
			iterate(V1);
			System.out.println("-----------------------");
	//		iterate(W);
			System.out.println("-----------------------");
			iterate(W1);
			System.out.println("-----------------------");*/
			
			// Ordering the predicates based on cardinality of the sample joins
			
		//	ArrayList<Integer> sampleOrder = new ArrayList<Integer>();// 
			long start = System.currentTimeMillis();
			ArrayList<Integer> sampleOrder = getPredicateOrdering(qd.Predicates, qd.Ordering);
		//	sampleOrder.add(0);
		//	sampleOrder.add(2);
		//	sampleOrder.add(1);
		//	sampleOrder.add(3);
			
		/*	for(int i=0;i<sampleOrder.size();i++)
			{
				System.out.println(sampleOrder.get(i));
			}*/
			System.out.println("Sampling took "+(System.currentTimeMillis()-start)/1000F+" seconds.");
			start = System.currentTimeMillis();
			ArrayList<Intermediates> inter = processLeftDeep(sampleOrder,qd);
			performJoin(qd, inter);
			System.out.println("Join took "+(System.currentTimeMillis()-start)/1000F+" seconds.");
			for(int i=0;i<inter.size();i++)
			{
				System.out.println(inter.get(i).file.cardinality);
			}
			
//			reArrange(R, sampleOrder);
			//	iterate(R);
			
			// Create the ordering. Must comment it
		/*	ArrayList<String> ordering = new ArrayList<String>();
			ordering.add("salary");
			ordering.add("tax");
			ordering.add("start");
			ordering.add("end");
			
			// Create the mapping. Must comment it
			HashMap<String,Integer> mapping1 = new HashMap<String,Integer>();
			mapping1.put("salary", 3);
			mapping1.put("tax", 4);
			
			HashMap<String,Integer> mapping2 = new HashMap<String,Integer>();
			mapping2.put("tax", 4);
			mapping2.put("start", 6);
			mapping2.put("salary", 3);
			mapping2.put("end", 7);
			
			// Scan the CSV files and generate the HeapFiles
			R = getHeapFile("F1r.csv", getOrdering(ordering, mapping1));
			//heapScan(R.FileName, R.Rtypes, R.Rsizes);
			//iterate(R1);
			//System.out.println("XXXXXXXXXXXXXXXXXXXXX");
			//iterate(R);
			//System.out.println("-----------------------------------------");
			S = getHeapFile("F2r.csv", getOrdering(ordering, mapping2));
			//heapScan(S.FileName, S.Rtypes, S.Rsizes);
			//iterate(S1);
			//System.out.println("XXXXXXXXXXXXXXXXXXXXX");
			//iterate(S);
			//System.out.println("-----------------------------------------");
			
			QueryDetails qd = parseQuery();
			// Populate and must comment
			CondExpr[] outFilter = new CondExpr[2];
			outFilter[0] = new CondExpr();
			outFilter[0].next = null;
			outFilter[0].op = new AttrOperator(1);
			outFilter[0].type1 = new AttrType(AttrType.attrSymbol);
			outFilter[0].type2 = new AttrType(AttrType.attrSymbol);
			outFilter[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), 3);
			outFilter[0].operand2.symbol = new FldSpec(new RelSpec(RelSpec.innerRel), 3);
			outFilter[1] = new CondExpr();
			outFilter[1].next = null;
			outFilter[1].op = new AttrOperator(1);
			outFilter[1].type1 = new AttrType(AttrType.attrSymbol);
			outFilter[1].type2 = new AttrType(AttrType.attrSymbol);
			outFilter[1].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), 4);
			outFilter[1].operand2.symbol = new FldSpec(new RelSpec(RelSpec.innerRel), 4);
			
			ArrayList<FldSpec> p = new ArrayList<FldSpec>();
			p.add(new FldSpec(new RelSpec(RelSpec.outer), 1));
			p.add(new FldSpec(new RelSpec(RelSpec.innerRel), 1));
		//	p.add(new FldSpec(new RelSpec(RelSpec.outer), 5));
		//	p.add(new FldSpec(new RelSpec(RelSpec.innerRel), 5));
			FldSpec[] proj1 = new FldSpec[p.size()];
			p.toArray(proj1);
			FileVariable joinedFile = joinFile(outFilter, proj1, R, S);
			int Cardinality = joinCardinality(outFilter, proj1, R, S);
			//iterate(joinedFile);
			//System.out.println("Cardinality : "+ Cardinality);
			
			
			ArrayList<PredicatePair> ppp = new ArrayList<PredicatePair>();
			Predicate p1 = new Predicate("R","1","S","1",1);
			Predicate p2 = new Predicate("R","2","S","2",1);
			PredicatePair pp = new PredicatePair(p1,p2);
			ppp.add(pp);
			
			Predicate p3 = new Predicate("R","1","S","1",1);
			Predicate p4 = new Predicate("R","2","S","2",2);
			PredicatePair pp1 = new PredicatePair(p3,p4);
			ppp.add(pp1);
			
			Predicate p5 = new Predicate("R","1","S","1",2);
			Predicate p6 = new Predicate("R","2","S","2",1);
			PredicatePair pp2 = new PredicatePair(p5,p6);
			ppp.add(pp2);
			
			Predicate p7 = new Predicate("R","1","S","1",2);
			Predicate p8 = new Predicate("R","2","S","2",2);
			PredicatePair pp3 = new PredicatePair(p7,p8);
			ppp.add(pp3);
		
			
			ArrayList<Integer> order = getPredicateOrdering(ppp);
			for(int i=0;i<order.size();i++)
			{
				System.out.println(order.get(i));
			}
		//	T = getHeapFile("F3r.csv", ordering);
		//	heapScan(T.FileName, T.Rtypes, T.Rsizes);
		//	System.out.println("-----------------------------------------");
		//	V = getHeapFile("F4r.csv", ordering);
		//	heapScan(V.FileName, V.Rtypes, V.Rsizes);
		//	System.out.println("-----------------------------------------");
		//	W = getHeapFile("F5r.csv", ordering);
		//	heapScan(W.FileName, W.Rtypes, W.Rsizes);
		//	System.out.println("-----------------------------------------");*/
			
		} 
		catch (HFException | HFBufMgrException | HFDiskMgrException | IOException e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}