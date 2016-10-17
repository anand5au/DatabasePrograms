package tests;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import btree.IntegerKey;
import bufmgr.PageNotReadException;
import global.AttrOperator;
import global.AttrType;
import global.GlobalConst;
import global.RID;
import global.SystemDefs;
import heap.FieldNumberOutOfBoundException;
import heap.Heapfile;
import heap.InvalidTupleSizeException;
import heap.InvalidTypeException;
import heap.Scan;
import heap.Tuple;
import iterator.CondExpr;
import iterator.FileScan;
import iterator.FldSpec;
import iterator.JoinsException;
import iterator.NestedLoopsJoins;
import iterator.PredEvalException;
import iterator.RelSpec;
import iterator.UnknowAttrType;
import iterator.WrongPermat;

public class InequalityJoin implements GlobalConst 
{
	private static void createDB() 
	{
		// Create the system definition
		String dbpath = "/tmp/" + System.getProperty("user.name") + ".minibase.jointestdb";
		String logpath = "/tmp/" + System.getProperty("user.name") + ".joinlog";

		String remove_cmd = "/bin/rm -rf ";
		String remove_logcmd = remove_cmd + logpath;
		String remove_dbcmd = remove_cmd + dbpath;
		String remove_joincmd = remove_cmd + dbpath;

		try {
			Runtime.getRuntime().exec(remove_logcmd);
			Runtime.getRuntime().exec(remove_dbcmd);
			Runtime.getRuntime().exec(remove_joincmd);
		} catch (IOException e) {
			System.err.println("" + e);
		}

		SystemDefs sysdef = new SystemDefs(dbpath, 1000, NUMBUF, "Clock");
		
	}
	
	
	private static void heapScan(Heapfile f, AttrType[] Stypes, short[] Ssizes) throws JoinsException, PageNotReadException, PredEvalException, UnknowAttrType, FieldNumberOutOfBoundException, WrongPermat 
	{
		FldSpec[] Sprojection = new FldSpec[4];
		Sprojection[0] = new FldSpec(new RelSpec(RelSpec.outer), 1);
		Sprojection[1] = new FldSpec(new RelSpec(RelSpec.outer), 2);
		Sprojection[2] = new FldSpec(new RelSpec(RelSpec.outer), 3);
		Sprojection[3] = new FldSpec(new RelSpec(RelSpec.outer), 4);
		
		FileScan am = null;
		try 
		{
			am = new FileScan("R.in", Stypes, Ssizes, (short) 4, (short) 4, Sprojection, null);
		} 
		catch (Exception e) 
		{
			System.err.println("" + e);
		}
		Tuple t = new Tuple();
		try
		{
			t.setHdr((short) Stypes.length, Stypes, Ssizes);
			t = am.get_next();
			while(t != null)
			{
				System.out.println(t.getIntFld(1));
				System.out.println(t.getIntFld(2));
				System.out.println(t.getIntFld(3));
				System.out.println(t.getIntFld(4));
				t = am.get_next();
				System.out.println("---");
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
	
	private static void createRelations()
	{
		// Create Relation R
		iterator.Iterator am = null;
		AttrType[] Rtypes  = new AttrType[0];
		short[] Rsizes = new short[0];
		int mRsize = 0;
		try
		{
			BufferedReader br = new BufferedReader(new FileReader(new File("R.txt")));
			int count = 0;
			int size=0;
			RID rid;
    		Heapfile fr = null;
			Tuple t = new Tuple();
			String strAttr[] = new String[0];
		    for(String line; (line = br.readLine()) != null; ) 
		    {
		    	if(count == 0)
		    	{
		    		int strCount = 0;
		    		strAttr = line.split(",");
		    		Rtypes = new AttrType[strAttr.length];
		    		for(int i=0;i<strAttr.length;i++)
		    		{
		    			strAttr[i].trim();
		    		//	if(strAttr[i].equals("attrInteger"))
		    		//		System.out.println(strAttr[i]);
		    			switch(strAttr[i])
		    			{
		    				case "attrString":
		    					Rtypes[i] = new AttrType(AttrType.attrString);
		    					strCount++;
		    					break;
		    				case "attrInteger":
		    					Rtypes[i] = new AttrType(AttrType.attrInteger);
		    					break;
		    				case "attrReal":
		    					Rtypes[i] = new AttrType(AttrType.attrReal);
		    					break;
		    			}
		    		}
		    		if(strCount>0)
		    		{
		    			Rsizes = new short[strCount];
			    		for(int i=0;i<Rsizes.length;i++)
			    		{
			    			Rsizes[i]=30;
			    		}
		    		}
		    	/*	System.out.println(Stypes.length);
		    		for(int i=0;i<Stypes.length;i++)
		    		{
		    			System.out.println(Stypes[i].attrType+" dsds");
		    		}*/
		    		t = new Tuple();
		    		t.setHdr((short) Rtypes.length, Rtypes, Rsizes);
		    		size = t.size();
		    		fr = new Heapfile("R.in");
		    		t = new Tuple(size);
		    		t.setHdr((short) Rtypes.length, Rtypes, Rsizes);
		    		count++;
		    		continue;
		    	}
		    //	System.out.println(t.noOfFlds());
		    	String str[] = line.split(",");
		    	for(int i=0;i<str.length;i++)
		    	{
		    		switch(strAttr[i])
			    		{
			    			case "attrString":
			    				t.setStrFld(i+1, str[i]);
			    				break;
			    			case "attrInteger":
			    				t.setIntFld(i+1, Integer.parseInt(str[i]));
			    			//	System.out.println((i+1)+"  "+Integer.parseInt(str[i]));
			    				break;
			    			case "attrReal":
			    				t.setFloFld(i+1, Float.parseFloat(str[i]));
			    				break;
			    		}
		    	}
		    	rid = fr.insertRecord(t.returnTupleByteArray());
		    }
		    // Create a file scan iterator of R relation
		    FldSpec[] Sprojection = new FldSpec[Rtypes.length];  	
	    	for(int i=0;i<Rtypes.length;i++)
	    	{
	    		Sprojection[i] = new FldSpec(new RelSpec(RelSpec.outer), i+1);
	    	}
	    	am = null;
			try
			{
				am = new FileScan("R.in", Rtypes, Rsizes, (short) 4, (short) 4, Sprojection, null);
				mRsize = Rtypes.length;
			} 
			catch (Exception e) 
			{
				System.err.println("" + e);
			}
		  //  heapScan(fr, Stypes, Ssizes);
		} 
		catch (Exception e) 
		{
			e.printStackTrace();
		}
		
		// Create Relation S
		
		try
		{
			BufferedReader br = new BufferedReader(new FileReader(new File("S.txt")));
			int count = 0;
			int size=0;
			RID rid;
    		Heapfile fs = null;
			Tuple t = new Tuple();
			short[] Ssizes = new short[0];
			String strAttr[] = new String[0];
			AttrType[] Stypes = new AttrType[0];
		    for(String line; (line = br.readLine()) != null; ) 
		    {
		    	if(count == 0)
		    	{
		    		int strCount = 0;
		    		strAttr = line.split(",");
		    		Stypes = new AttrType[strAttr.length];
		    		for(int i=0;i<strAttr.length;i++)
		    		{
		    			strAttr[i].trim();
		    		//	if(strAttr[i].equals("attrInteger"))
		    		//		System.out.println(strAttr[i]);
		    			switch(strAttr[i])
		    			{
		    				case "attrString":
		    					Stypes[i] = new AttrType(AttrType.attrString);
		    					strCount++;
		    					break;
		    				case "attrInteger":
		    					Stypes[i] = new AttrType(AttrType.attrInteger);
		    					break;
		    				case "attrReal":
		    					Stypes[i] = new AttrType(AttrType.attrReal);
		    					break;
		    			}
		    		}
		    		if(strCount>0)
		    		{
		    			Ssizes = new short[strCount];
			    		for(int i=0;i<Ssizes.length;i++)
			    		{
			    			Ssizes[i]=30;
			    		}
		    		}
		    	/*	System.out.println(Stypes.length);
		    		for(int i=0;i<Stypes.length;i++)
		    		{
		    			System.out.println(Stypes[i].attrType+" dsds");
		    		}*/
		    		t = new Tuple();
		    		t.setHdr((short) Stypes.length, Stypes, Ssizes);
		    		size = t.size();
		    		fs = new Heapfile("S.in");
		    		t = new Tuple(size);
		    		t.setHdr((short) Stypes.length, Stypes, Ssizes);
		    		count++;
		    		continue;
		    	}
		    	String str[] = line.split(",");
		    	for(int i=0;i<str.length;i++)
		    	{
		    		switch(strAttr[i])
			    		{
			    			case "attrString":
			    				t.setStrFld(i+1, str[i]);
			    				break;
			    			case "attrInteger":
			    				t.setIntFld(i+1, Integer.parseInt(str[i]));
			    				break;
			    			case "attrReal":
			    				t.setFloFld(i+1, Float.parseFloat(str[i]));
			    				break;
			    		}
		    	}
		    	rid = fs.insertRecord(t.returnTupleByteArray());
		    }
		    
		    // Get the input query and prepare the projection list and conditon expressions
		    class predicate 
			{
				String table1;
				int column1;
				String table2;
				int column2;
				int operation;
			}
		    
		    // Get the select fields
		    FldSpec[] proj1;
		    ArrayList<FldSpec> p = new ArrayList<FldSpec>();
		    String line = null;
			HashMap<String, ArrayList<Integer>> selectclause = new HashMap<String, ArrayList<Integer>>();
			String[] linearray;
			String[] singleselection;
			ArrayList<Integer> columns = new ArrayList<Integer>();
			ArrayList<String> tables = new ArrayList<String>();
			ArrayList<predicate> predicates = new ArrayList<predicate>();
			FileReader in = new FileReader("query_1a.txt");
			BufferedReader br2 = new BufferedReader(in);
			br2.readLine();
			String relations[] = br2.readLine().split((" "));
			String outerrel = relations[0].trim();
			String innerrel = relations[1].trim();
			br2.close();
			in.close();
			in = new FileReader("query_1a.txt");
			BufferedReader br1 = new BufferedReader(in);
			//System.out.println(outerrel);
			if ((line = br1.readLine()) != null) {
			//	System.out.println(line);
				linearray = line.split(" ");
				for (int i = 0; i < linearray.length; i++) 
				{
					columns = new ArrayList<Integer>();
					singleselection = linearray[i].split("_");
					if (selectclause.containsKey(singleselection[0])) 
					{
						columns = selectclause.get(singleselection[0]);
					}
					columns.add(Integer.parseInt(singleselection[1]));
					selectclause.put(singleselection[0], columns);
				//	System.out.println("The select clause is " + singleselection[0] + columns + "\n");
					if(singleselection[0].equals(outerrel))
					{
						p.add(new FldSpec(new RelSpec(RelSpec.outer), Integer.parseInt(singleselection[1])));
					}
					else
						p.add(new FldSpec(new RelSpec(RelSpec.innerRel), Integer.parseInt(singleselection[1])));
				}
			}
			proj1 = new FldSpec[p.size()];
			p.toArray(proj1);
			line = br1.readLine();
			// Parse the predicates
			while ((line = br1.readLine()) != null) {
				predicate temp = new predicate();
				linearray = line.split(" ");
				singleselection = linearray[0].split("_");
				temp.table1 = singleselection[0];
				temp.column1 = Integer.parseInt(singleselection[1]);
				temp.operation = Integer.parseInt(linearray[1]);
				singleselection = linearray[2].split("_");
				temp.table2 = singleselection[0];
				temp.column2 = Integer.parseInt(singleselection[1]);
				predicates.add(temp);
		/*		System.out.println("The table1 is " + temp.table1 +
						" and the column1 is " + temp.column1 +
						" and the table2 is " + temp.table2 +
						" and the column2 is " + temp.column2 +
						" and the operation is " + temp.operation + "\n");*/
				if(br1.readLine() == null)
					break;
			}
			CondExpr[] outFilter = new CondExpr[predicates.size()+1];
			for(int i=0;i<outFilter.length;i++)
			{
				outFilter[i] = new CondExpr();
			}
			for(int i=0;i<predicates.size();i++)
			{
			//	System.out.println(" c1 "+predicates.get(i).column1+"  c2: "+predicates.get(i).column2+ " op "+predicates.get(i).operation);
				outFilter[i].next = null;
				outFilter[i].op = new AttrOperator(predicates.get(i).operation);
				outFilter[i].type1 = new AttrType(AttrType.attrSymbol);
				outFilter[i].type2 = new AttrType(AttrType.attrSymbol);
				outFilter[i].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), predicates.get(i).column1);
				outFilter[i].operand2.symbol = new FldSpec(new RelSpec(RelSpec.innerRel), predicates.get(i).column2);
			}
			outFilter[predicates.size()] = null;
			br1.close();
			in.close();
		  
		    // Do the nested loop join
		    NestedLoopsJoins nlj = null;
		    long start = System.currentTimeMillis();
		    long freemem = Runtime.getRuntime().freeMemory();
			try 
			{
				nlj = new NestedLoopsJoins(Rtypes, Rtypes.length, Rsizes, Stypes, Stypes.length, Ssizes, 10, am, "S.in", 
						outFilter, null, proj1, proj1.length);
				System.out.println("Sort Iterator got in "+(System.currentTimeMillis()-start)+" mseconds");
				System.out.println("Memory used : " + (Runtime.getRuntime().freeMemory()-freemem));
			} 
			
			catch (Exception e)
			{
				System.err.println("*** Error preparing for nested_loop_join");
				System.err.println("" + e);
				e.printStackTrace();
				Runtime.getRuntime().exit(1);
			}
			
			Tuple t1 = nlj.get_next();
			int car = 0;
			start = System.currentTimeMillis();
			while(t1!=null)
			{
				System.out.print(t1.getIntFld(1)+" x ");
				System.out.println(t1.getIntFld(2));
				t1 = nlj.get_next();
				car++;
				// System.out.println("----");
			}
			System.out.println("Result got in "+(System.currentTimeMillis()-start)+" mseconds");
			System.out.println("Cardinality " +car);
			
		   // heapScan(fs, Stypes, Ssizes);
		} 
		catch (Exception e) 
		{
			e.printStackTrace();
		}
		
		
	}

	public static void main(String args[])
	{
		createDB();
		createRelations();
	}
}
