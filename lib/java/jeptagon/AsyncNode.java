package jeptagon;

import java.util.concurrent.Future;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.Callable;
import java.util.concurrent.FutureTask;

public class AsyncNode<T> {
	
	protected final ArrayBlockingQueue<FutureTask<T>>[] queue;
	protected int currentQueue;
	protected final int queueNb;
	protected final Thread[] t;
	
	protected class AsyncNodeThread extends Thread {
		protected final int queueId;
		public AsyncNodeThread(int queueId) {
			this.queueId = queueId;
		}
		public void run() {
			try {
				while (true) queue[queueId].take().run();
			}
			catch (InterruptedException e) {
				return;
			}		
		}
	}
		
	@SuppressWarnings("unchecked")
	public AsyncNode(int queueNb, int queueSize) {
		if (queueNb<1) { java.lang.System.err.println("asyncnode given with 0 thread to execute"); }
		this.queue = new ArrayBlockingQueue[queueNb];
		this.t = new Thread[queueNb];
		this.currentQueue = 0;
		this.queueNb = queueNb;
		for (int i = 0; i<queueNb; i++) {
			this.queue[i] = new ArrayBlockingQueue<FutureTask<T>>(queueSize,false);
			t[i] = new AsyncNodeThread(i);
			t[i].start();
		}
	}
	
	public Future<T> submit(Callable<T> c) {
		FutureTask<T> t = new FutureTask<T>(c);
		try {
			queue[currentQueue].put(t);
		}
		catch (InterruptedException e) { e.printStackTrace(); }
		return (Future<T>) t;
	}


	public void reset() {
		// the heuristic is to use the available threads in a round-robin manner.
		currentQueue = (currentQueue + 1) % queueNb;
	}
	
		
	public void shutdown() {
		for (int i = 0; i<queueNb; i++) {
			t[i].interrupt();
		}
		return;
	}
	
	protected void finalize() throws Throwable {
		 try { shutdown(); }
		 finally { super.finalize(); }
	}
}