/* File LRUK.java */

package bufmgr;

import diskmgr.*;
import global.*;
import java.util.*;

/**
 * class LRUK is a subclass of class Replacer using LRUK algorithm for page
 * replacement
 */
public class LRUK extends Replacer
{

	/**
	 * private field An array to hold number of frames in the buffer pool
	 */

	private int frames[];

	/**
	 * private field number of frames used
	 */
	private int nframes;

	/**
	 * private field A map that has history of access times of all pages in
	 * buffer
	 */
	private HashMap<Integer, LinkedList<Long>> hist;
	
	private HashMap<Integer, Long> last;

	public static final double Correlation_Reference_period = 0.001; // 1
	                                                                 // microsecond
	public static final int K = 15;

	/**
	 * private field A list that has timestamps of last access of all pages in
	 * buffer
	 */
	public long LAST(int pgId)
	{
		return last.get(pgId);
	}

	public long HIST(int pgId, int n)
	{
		return hist.get(pgId).get(n - 1);
	}

	public long back(int pgId, int n)
	{
		return LAST(pgId) - HIST(pgId, n);
	}

	/**
	 * private field returns the array holding frames in the buffer pool
	 */
	public int[] getFrames()
	{
		return frames;
	}

	/**
	 * This pushes the given frame to the end of the list.
	 * 
	 * @param frameNo
	 *            the frame number
	 */
	private void update(int frameNo)
	{
		int index;
		for (index = 0; index < nframes; ++index)
			if (frames[index] == frameNo)
				break;

		while (++index < nframes)
			frames[index - 1] = frames[index];
		frames[nframes - 1] = frameNo;
	}

	/**
	 * Calling super class the same method Initializing the frames[] with number
	 * of buffer allocated by buffer manager set number of frame used to zero
	 *
	 * @param mgr
	 *            a BufMgr object
	 * @see BufMgr
	 * @see Replacer
	 */
	public void setBufferManager(BufMgr mgr)
	{
		super.setBufferManager(mgr);
		frames = new int[mgr.getNumBuffers()];
		nframes = 0;
		hist = new HashMap<Integer, LinkedList<Long>>();
		last = new HashMap<Integer,Long>();
	}

	/**
	 * Class constructor Initializing frames[] pinter = null.
	 */
	public LRUK(BufMgr mgrArg)
	{
		super(mgrArg);
		frames = null;
		hist = null;
	}

	/**
	 * calll super class the same method pin the page in the given frame number
	 * move the page to the end of list
	 *
	 * @param frameNo
	 *            the frame number to pin
	 * @exception InvalidFrameNumberException
	 */
	public void pin(int frameNo) throws InvalidFrameNumberException
	{
		super.pin(frameNo);

		update(frameNo);

	}

	/**
	 * Finding a free frame in the buffer pool or choosing a page to replace
	 * using LRUK policy
	 *
	 * @return return the frame number return -1 if failed
	 */

	public int pick_victim() throws BufferPoolExceededException, PagePinnedException
	{
		int numBuffers = mgr.getNumBuffers();
		int frame = -1;

		Long t = System.currentTimeMillis();
		if (hist.containsKey(mgr.pg_id))
		{
			hist.get(mgr.pg_id).addFirst(t);
		}
		else
		{
			LinkedList<Long> l = new LinkedList<Long>();
			for (int i = 0; i < K - 1; i++)
				l.addFirst((long) 0);
			l.addFirst(t);
			hist.put(mgr.pg_id, l);
		}
		last.put(mgr.pg_id, t);
		
		
		if (nframes < numBuffers)
		{
			frame = nframes++;
			frames[frame] = frame;
			state_bit[frame].state = Pinned;
			(mgr.frameTable())[frame].pin();
			return frame;
		}

		long min = t;
		int victim = -1;
		for (int i = 0; i < mgr.frameTable().length; ++i)
		{
			int pg = mgr.frameTable()[i].pageNo.pid;
			if(pg == -1)
			{
				victim = i;
				break;
			}
			if ((state_bit[i].state != Pinned) && (t - LAST(i) > Correlation_Reference_period)
			        && (HIST(i, K) < min))
			{
				victim = i;
				min = HIST(i, K);
			}
		}
		
		if (victim > -1)
		{
			state_bit[victim].state = Pinned;
			(mgr.frameTable())[victim].pin();
			update(victim);
			return victim;
		}
		
		throw new BufferPoolExceededException(null, "BUFMGR: BUFFER_EXCEEDED.");
		
	}

	/**
	 * get the page replacement policy name
	 *
	 * @return return the name of replacement policy used
	 */
	public String name()
	{
		return "LRU-K";
	}

	/**
	 * print out the information of frame usage
	 */
	public void info()
	{
		super.info();

		System.out.print("LRU-K REPLACEMENT");

		for (int i = 0; i < nframes; i++)
		{
			if (i % 5 == 0)
				System.out.println();
			System.out.print("\t" + frames[i]);

		}
		System.out.println();
	}

}
