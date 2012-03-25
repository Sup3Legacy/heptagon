package Do;

public class FUNS {
	public static int stuff(int coeff) {
                int x = 13;
                for (int i = 0; i < coeff; i++) {
                        for (int j = 0; j < 1000000; j++) {
                                x = (x + j) % (x + j/x) + 13;
                        }
                }
                return 0;
        }
}
