package forbiden;

import java.util.concurrent.Future;

enum E { e1, e2 }

public class Forbiden {
//	void array_of_generics () {
//		Future<Integer>[] m = new Future<Integer>[N];
//	}
	int init_match (E e) {
		int x;
		switch(e) {
		case e1 :
			x = 0;
			break;
		case e2 :
			x = 1;
			break;
		default :
			throw new AssertionError();
		}
		return x;
	}
	
}
