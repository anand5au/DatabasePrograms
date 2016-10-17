package bufmgr;

import java.io.*;
import java.util.*;
import diskmgr.*;
import global.*;

/**
 * FIFO algorithm for buffer pool replacement policy. It picks up the frame in
 * the buffer pool to be replaced.
 */
public class FIFO extends Replacer
{

	private int frames[];

	/**
	 * private field number of frames used
	 */
	private int nframes;

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
	}

	/* public methods */

	/**
	 * Class constructor Initializing frames[] pinter = null.
	 */
	public FIFO(BufMgr mgrArg)
	{
		super(mgrArg);
		frames = null;
	}

	/**
	 * Finding a free frame in the buffer pool or choosing a page to replace
	 * using FIFO policy
	 *
	 * @return return the frame number return -1 if failed
	 */

	public int pick_victim() throws BufferPoolExceededException, PagePinnedException
	{
		int numBuffers = mgr.getNumBuffers();
		int frame;

		if (nframes < numBuffers)
		{
			frame = nframes++;
			frames[frame] = frame;
			state_bit[frame].state = Pinned;
			(mgr.frameTable())[frame].pin();
			return frame;
		}

		for (int i = 0; i < numBuffers; ++i)
		{
			frame = frames[i];
			if (state_bit[frame].state != Pinned)
			{
				state_bit[frame].state = Pinned;
				(mgr.frameTable())[frame].pin();
				update(frame);
				return frame;
			}
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
		return "FIFO";
	}

	/**
	 * print out the information of frame usage
	 */
	public void info()
	{
		super.info();

		System.out.print("FIFO REPLACEMENT - Used frames");

		for (int i = 0; i < nframes; i++)
		{
			if (i % 5 == 0)
				System.out.println();
			System.out.print("\t" + frames[i]);

		}
		System.out.println();
	}

}
