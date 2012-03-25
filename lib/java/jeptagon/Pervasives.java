package jeptagon;

import java.lang.reflect.Array;
import java.util.Arrays;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public class Pervasives {

	public static int between(int i, int m) {
		if (i<0) {
			java.lang.System.err.printf("%d ! >= 0\n",i);
			return 0;
		}
		else if (i>=m) {
			java.lang.System.err.printf("%d ! < %d\n",i,m);
			return m-1;
		}
		else return i;
	}
	public static int int_of_bool(boolean b) {
		return b?1:0;
	}

	public static boolean bool_of_int(int i) {
		return i!=0;
	}

	public static final ExecutorService executor_cached = Executors.newCachedThreadPool();
	public static final int max_tasks = 25;

	public static class StaticFuture<V> implements Future<V> {
		V v;

		public StaticFuture(V v) { this.v = v;	}

		public boolean cancel(boolean mayInterruptIfRunning) { return false; }

		public boolean isCancelled() { return false; }

		public boolean isDone() { return true; }

		public V get() { return v; }

		public V get(long timeout, TimeUnit unit) { return v; }
	}

	public static class FutureOfFuture<V,T> implements Future<V> {
		Future<T> t;
		String field;
		public FutureOfFuture(Future<T> t, String field) {
			this.t = t;
			this.field = field;
		}
		public boolean cancel(boolean arg0) { return false;	}

		@SuppressWarnings("unchecked")
		public V get() throws InterruptedException, ExecutionException {
			T o = t.get();
			try {
				return ((V) o.getClass().getField(field).get(o));
			} catch (IllegalArgumentException e) {
				e.printStackTrace();
			} catch (SecurityException e) {
				e.printStackTrace();
			} catch (IllegalAccessException e) {
				e.printStackTrace();
			} catch (NoSuchFieldException e) {
				e.printStackTrace();
			}
			return null;
		}

		public V get(long arg0, TimeUnit arg1) throws InterruptedException, ExecutionException {
			return get();
		}

		public boolean isCancelled() { return t.isCancelled(); }

		public boolean isDone() { return t.isDone(); }

	}

    //faster version for primitive arrays using serializing
    public static Object copyNd(Object arr) {
        if (arr.getClass().isArray()) {
            int innerArrayLength = Array.getLength(arr);
            Class component = arr.getClass().getComponentType();
            Object newInnerArray = Array.newInstance(component, innerArrayLength);
            //copy each elem of the array
            for (int i = 0; i < innerArrayLength; i++) {
                Object elem = copyNd(Array.get(arr, i));
                Array.set(newInnerArray, i, elem);
            }
            return newInnerArray;
        } else {
            return arr;//cant deep copy an opac object??
        }
    }

	public static String genToString(Object c) {
		Class<?> cClass = c.getClass();
		if (cClass.isArray()) {
			switch (cClass.getName().charAt(1)) { //charAt(0) is '['
			case 'B' : return Arrays.toString((byte[]) c);
			case 'C' : return Arrays.toString((char[]) c);
			case 'D' : return Arrays.toString((double[]) c);
			case 'F' : return Arrays.toString((float[]) c);
			case 'I' : return Arrays.toString((int[]) c);
			case 'J' : return Arrays.toString((long[]) c);
			case 'S' : return Arrays.toString((short[]) c);
			case 'Z' : return Arrays.toString((boolean[]) c);
			default : //L or [
				return Arrays.deepToString((Object [])c);
			}
		} else
		return c.toString();
	}

	public static class Tuple1 {
		public final Object c0;
		public Tuple1(Object v) {
			c0 = v;
		}
		public String toString() {
			return "(" + genToString(c0) + ")";
		}
	}

	public static class Tuple2 {
		public final Object c0;
		public final Object c1;
		public Tuple2(Object v0, Object v1) {
			c0 = v0;
			c1 = v1;
		}
		public String toString() {
			return "(" + genToString(c0) + ", " + genToString(c1) + ")";
		}
	}
	
	public static Tuple2 at_to_ta2 ( final Future<Tuple2> at) {
		FutureTask t0 = new FutureTask(new Callable () {
			public Object call() throws Exception {
				return at.get().c0;
			} });
		FutureTask t1 = new FutureTask(new Callable () {
			public Object call() throws Exception {
				return at.get().c1;
			} });
		return new Tuple2(t0,t1);
	}

	public static class Tuple3 {
		public final Object c0;
		public final Object c1;
		public final Object c2;
		public Tuple3(Object v0, Object v1, Object v2) {
			c0 = v0;
			c1 = v1;
			c2 = v2;
		}
		public String toString() {
			return "(" + genToString(c0) + ", " + genToString(c1) + ", " + genToString(c2) + ")";
		}
	}

	public static Tuple3 at_to_ta3 ( final Future<Tuple3> at) {
		FutureTask t0 = new FutureTask(new Callable () {
			public Object call() throws Exception {
				return at.get().c0;
			} });
		FutureTask t1 = new FutureTask(new Callable () {
			public Object call() throws Exception {
				return at.get().c1;
			} });
		FutureTask t2 = new FutureTask(new Callable () {
			public Object call() throws Exception {
				return at.get().c2;
			} });
		return new Tuple3(t0,t1,t2);
	}

	public static class Tuple4 {
		public final Object c0;
		public final Object c1;
		public final Object c2;
		public final Object c3;
		public Tuple4(Object v0, Object v1, Object v2, Object v3) {
			c0 = v0;
			c1 = v1;
			c2 = v2;
			c3 = v3;
		}
		public String toString() {
			return "(" + genToString(c0) + ", " + genToString(c1)
			+ ", " + genToString(c2) + ", " + genToString(c3) + ")";
		}
	}

	public static class Tuple5 {
		public final Object c0;
		public final Object c1;
		public final Object c2;
		public final Object c3;
		public final Object c4;
		public Tuple5(Object v0, Object v1, Object v2, Object v3, Object v4) {
			c0 = v0;
			c1 = v1;
			c2 = v2;
			c3 = v3;
			c4 = v4;
		}
		public String toString() {
			return "(" + genToString(c0) + ", " + genToString(c1) + ", " + genToString(c2)
			+ ", " + genToString(c3) + ", " + genToString(c4) + ")";
		}
	}

	public static class Tuple6 {
		public final Object c0;
		public final Object c1;
		public final Object c2;
		public final Object c3;
		public final Object c4;
		public final Object c5;
		public Tuple6(Object v0, Object v1, Object v2, Object v3, Object v4, Object v5) {
			c0 = v0;
			c1 = v1;
			c2 = v2;
			c3 = v3;
			c4 = v4;
			c5 = v5;
		}
		public String toString() {
			return "(" + genToString(c0) + ", " + genToString(c1) + ", " + genToString(c2)
			+ ", " + genToString(c3) + ", " + genToString(c4) + ", " + genToString(c5) + ")";
		}
	}

	public static class Tuple7 {
		public final Object c0;
		public final Object c1;
		public final Object c2;
		public final Object c3;
		public final Object c4;
		public final Object c5;
		public final Object c6;
		public Tuple7(Object v0, Object v1, Object v2, Object v3, Object v4, Object v5, Object v6) {
			c0 = v0;
			c1 = v1;
			c2 = v2;
			c3 = v3;
			c4 = v4;
			c5 = v5;
			c6 = v6;
		}
		public String toString() {
			return "(" + genToString(c0) + ", " + genToString(c1) + ", " + genToString(c2)
			+ ", " + genToString(c3) + ", " + genToString(c4) + ", " + genToString(c5)
			+ ", " + genToString(c6) + ")";
		}
	}

	public static class Tuple8 {
		public final Object c0;
		public final Object c1;
		public final Object c2;
		public final Object c3;
		public final Object c4;
		public final Object c5;
		public final Object c6;
		public final Object c7;
		public Tuple8(Object v0, Object v1, Object v2, Object v3, Object v4, Object v5, Object v6, Object v7) {
			c0 = v0;
			c1 = v1;
			c2 = v2;
			c3 = v3;
			c4 = v4;
			c5 = v5;
			c6 = v6;
			c7 = v7;
		}
		public String toString() {
			return "(" + genToString(c0) + ", " + genToString(c1) + ", " + genToString(c2)
			+ ", " + genToString(c3) + ", " + genToString(c4) + ", " + genToString(c5)
			+ ", " + genToString(c6) + ", " + genToString(c7) + ")";
		}
	}

	public static class Tuple9 {
		public final Object c0;
		public final Object c1;
		public final Object c2;
		public final Object c3;
		public final Object c4;
		public final Object c5;
		public final Object c6;
		public final Object c7;
		public final Object c8;
		public Tuple9(Object v0, Object v1, Object v2, Object v3, Object v4, Object v5, Object v6, Object v7, Object v8) {
			c0 = v0;
			c1 = v1;
			c2 = v2;
			c3 = v3;
			c4 = v4;
			c5 = v5;
			c6 = v6;
			c7 = v7;
			c8 = v8;
		}
		public String toString() {
			return "(" + genToString(c0) + ", " + genToString(c1) + ", " + genToString(c2)
			+ ", " + genToString(c3) + ", " + genToString(c4) + ", " + genToString(c5)
			+ ", " + genToString(c6) + ", " + genToString(c7) + ", " + genToString(c8) + ")";
		}
	}

}
