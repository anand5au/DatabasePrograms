package tests;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import bufmgr.PageNotReadException;
import global.AttrOperator;
import global.AttrType;
import global.GlobalConst;
import global.RID;
import global.SystemDefs;
import global.TupleOrder;
import heap.FieldNumberOutOfBoundException;
import heap.Heapfile;
import heap.InvalidTupleSizeException;
import heap.InvalidTypeException;
import heap.Tuple;
import iterator.CondExpr;
import iterator.FileScan;
import iterator.FldSpec;
import iterator.JoinsException;
import iterator.LightningInequalitySelfJoin;
import iterator.PredEvalException;
import iterator.RelSpec;
import iterator.SelfJoin;
import iterator.SortMerge;
import iterator.UnknowAttrType;
import iterator.WrongPermat;

public class SelfJoinTest implements GlobalConst 
{
	iterator.Iterator am = null;
	iterator.Iterator am2 = null;
	AttrType[] Qtypes = new AttrType[0];
	short[] Qsizes = new short[0];
	FldSpec[] proj1 = new FldSpec[0];
	CondExpr[] outFilter = new CondExpr[0];
	int mRsize = 0;
	
	private static void heapScan(Heapfile f, AttrType[] Stypes, short[] Ssizes) throws JoinsException,
			PageNotReadException, PredEvalException, UnknowAttrType, FieldNumberOutOfBoundException, WrongPermat 
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
			while (t != null) 
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

	private static void createDB() 
	{
		// Create the system definition
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

		SystemDefs sysdef = new SystemDefs(dbpath, 1000, 500, "Clock");

	}

	private void createRelation() 
	{
		// Create Relation Q
		try 
		{
			BufferedReader br = new BufferedReader(new FileReader(new File("Q1.txt")));
			int count = 0;
			int size = 0;
			RID rid;
			Heapfile fr = null;
			Tuple t = new Tuple();
			String strAttr[] = new String[0];
			for (String line; (line = br.readLine()) != null;)
			{
				if (count == 0) 
				{
					int strCount = 0;
					strAttr = line.split(",");
					Qtypes = new AttrType[strAttr.length];
					for (int i = 0; i < strAttr.length; i++) 
					{
						strAttr[i].trim();
						// if(strAttr[i].equals("attrInteger"))
						// System.out.println(strAttr[i]);
						switch (strAttr[i]) 
						{
							case "attrString":
								Qtypes[i] = new AttrType(AttrType.attrString);
								strCount++;
								break;
							case "attrInteger":
								Qtypes[i] = new AttrType(AttrType.attrInteger);
								break;
							case "attrReal":
								Qtypes[i] = new AttrType(AttrType.attrReal);
								break;
						}
					}
					if (strCount > 0) 
					{
						Qsizes = new short[strCount];
						for (int i = 0; i < Qsizes.length; i++) {
							Qsizes[i] = 30;
						}
					}
					/*
					 * System.out.println(Stypes.length); for(int
					 * i=0;i<Stypes.length;i++) {
					 * System.out.println(Stypes[i].attrType+" dsds"); }
					 */
					t = new Tuple();
					t.setHdr((short) Qtypes.length, Qtypes, Qsizes);
					size = t.size();
					fr = new Heapfile("R.in");
					t = new Tuple(size);
					t.setHdr((short) Qtypes.length, Qtypes, Qsizes);
					count++;
					continue;
				}
				// System.out.println(t.noOfFlds());
				String str[] = line.split(",");
				for (int i = 0; i < str.length; i++)
				{
					switch (strAttr[i]) 
					{
						case "attrString":
							t.setStrFld(i + 1, str[i]);
							break;
						case "attrInteger":
							t.setIntFld(i + 1, Integer.parseInt(str[i]));
							// System.out.println((i+1)+"
							// "+Integer.parseInt(str[i]));
							break;
						case "attrReal":
							t.setFloFld(i + 1, Float.parseFloat(str[i]));
							break;
					}
				}
				rid = fr.insertRecord(t.returnTupleByteArray());
			}

			// Create a file scan iterator of R relation
			FldSpec[] Sprojection = new FldSpec[Qtypes.length];
			for (int i = 0; i < Qtypes.length; i++) 
			{
				Sprojection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);
			}
			am = null;
			am2 = null;
			try 
			{
				am = new FileScan("R.in", Qtypes, Qsizes, (short) 4, (short) 4, Sprojection, null);
				mRsize = Qtypes.length;
				am2 = new FileScan("R.in", Qtypes, Qsizes, (short) 4, (short) 4, Sprojection, null);
			} 
			catch (Exception e) 
			{
				System.err.println("" + e);
			}
			// heapScan(fr, Qtypes, Qsizes);
		}
		catch (Exception e)
		{
			e.printStackTrace();
		}
	}
	
	private void parseQuery() 
	{
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
	    ArrayList<FldSpec> p = new ArrayList<FldSpec>();
	    String line = null;
		String[] linearray;
		String[] singleselection;
		ArrayList<Integer> columns = new ArrayList<Integer>();
		ArrayList<String> tables = new ArrayList<String>();
		ArrayList<predicate> predicates = new ArrayList<predicate>();
		FileReader in;
		try 
		{
			in = new FileReader("query_2a.txt");
			BufferedReader br1 = new BufferedReader(in);
			HashSet<Integer> sel = new HashSet<Integer>();
			if ((line = br1.readLine()) != null) {
				//System.out.println(line);
				linearray = line.split(" ");
				for (int i = 0; i < linearray.length; i++) 
				{
					singleselection = linearray[i].split("_");
					if(!sel.contains(Integer.parseInt(singleselection[1])))
					{
						p.add(new FldSpec(new RelSpec(RelSpec.outer), Integer.parseInt(singleselection[1])));
					//	System.out.println("outer");
						sel.add(Integer.parseInt(singleselection[1]));
					}
					else
					{
					//	System.out.println("inner");
						p.add(new FldSpec(new RelSpec(RelSpec.innerRel), Integer.parseInt(singleselection[1])));
					}	
				}
			}
			proj1 = new FldSpec[p.size()];
			p.toArray(proj1);
			line = br1.readLine();
			// Parse the predicates
			while ((line = br1.readLine()) != null) 
			{
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
				if(br1.readLine() == null)
					break;
			}
			outFilter = new CondExpr[predicates.size()+1];
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
		} 
		catch (Exception e) 
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	private void join() 
	{
		SelfJoin sj = null;
		TupleOrder ascending = new TupleOrder(TupleOrder.Ascending);
		TupleOrder descending = new TupleOrder(TupleOrder.Descending);
		long start = System.currentTimeMillis();
		long freemem = Runtime.getRuntime().freeMemory();
		try 
		{
			if(outFilter[0].op.attrOperator == 2 || outFilter[0].op.attrOperator == 5)
			{
				sj = new SelfJoin(Qtypes, Qtypes.length, Qsizes, Qtypes, Qtypes.length, Qsizes, 
						outFilter[0].operand1.symbol.offset, 4, 
						10, am, am2, false, false, ascending, outFilter, proj1, 2);
			}
			else
			{
				sj = new SelfJoin(Qtypes, Qtypes.length, Qsizes, Qtypes, Qtypes.length, Qsizes, 
						outFilter[0].operand1.symbol.offset, 4, 
						10, am, am2, false, false, descending, outFilter, proj1, 2);
			}
			System.out.println("Sort iterator got in "+(System.currentTimeMillis()-start)+" mseconds");
			System.out.println("Memory used : " + (Runtime.getRuntime().freeMemory()-freemem)/(1024*1024));
			Tuple tuple = new Tuple();
			start = System.currentTimeMillis();
			int car = 0;
			while(( tuple = sj.get_next())!=null)
			{
				System.out.println(tuple.getIntFld(1)+" x "+tuple.getIntFld(2));
				car++;
			}
			System.out.println("Result got in "+(System.currentTimeMillis()-start)+" mseconds");
			//System.out.println("Cardinality "+ car);
			
		} 
		catch (Exception e) 
		{
			System.err.println("*** join error in SortMerge constructor ***");
			System.err.println("" + e);
			e.printStackTrace();
		}
	}

	public static void main(String args[]) 
	{
		createDB();
		SelfJoinTest light = new SelfJoinTest();
		light.createRelation();
		light.parseQuery();
		light.join();
	}

}
