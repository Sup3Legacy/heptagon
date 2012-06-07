package Ac;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;
import jeptagon.AsyncNode;
import jeptagon.AsyncFun;

public class Manual_A_pppgame {
    protected Async_factory_pppcore pppcore;
    protected Future<int[]>[] last_g;
    protected Future<int[]>[] last_ng;
    protected int last_stut_index;
    protected int last_stut_left_index;
    protected int last_stut_right_index;
    protected boolean newone;
    protected boolean reset;
    protected int v_2_1;
    protected final int N;
    protected final int K;
    protected final int RULE;
    protected final int[] FIRST;

    public Manual_A_pppgame (int N, int K, int RULE, int[] FIRST) {
        this.N = N;
        this.K = K;
        this.RULE = RULE;
        this.FIRST = FIRST;
        this.pppcore = new Async_factory_pppcore(2, K, N, RULE);
        this.last_g = new Future[K];
        this.last_ng = new Future[K];
        {
            this.reset = false;
            this.v_2_1 = 0;
            this.last_stut_right_index = -1;
            this.last_stut_index = -1;
            this.last_stut_left_index = -1;
            for (int i_16 = 0; i_16<K; i_16++) { this.last_g[i_16] = new jeptagon.Pervasives.StaticFuture(FIRST); }
            this.newone = true;
            for (int i_17 = 0; i_17<K; i_17++) { this.last_ng[i_17] = new jeptagon.Pervasives.StaticFuture(FIRST); }
        }
    }
    public int[][] step () throws java.lang.InterruptedException, java.util.concurrent.ExecutionException {
        int[][] y = new int[K][N];
        boolean __node_big_step = true;
        do {
            boolean v_14 = true;
            boolean v_12 = true;
            int v_13_v_11 = 0;
            boolean v_9 = true;
            int v_1_1_v_10_v_8 = 0;
            boolean v_7 = true;
            Future<int[]> v_5 = null;
            Future<int[]> v_3 = null;
            Future<int[]> v_2 = null;
            boolean v = true;
            int stut_index = 0;
            int stut_left_index = 0;
            int stut_right_index = 0;
            int index = 0;
            int left_index = 0;
            int right_index = 0;
            int stut_left = 0;
            int stut_right = 0;
            boolean swap = true;
            Future<int[]> chunk = null;
            v_7 = !this.newone;
            if (this.newone) {
                if (this.reset) {
                    index = 0;
                } else {
                    index = this.v_2_1;
                }
                v = (index == 0);
                v_1_1_v_10_v_8 = (index + 1);
                v_9 = (v_1_1_v_10_v_8 > (K - 1));
                swap = v;
                v_13_v_11 = (index - 1);
                v_12 = (v_13_v_11 < 0);
                v_14 = (index == (K - 1));
                this.reset = v_14;
                this.v_2_1 = v_1_1_v_10_v_8;
                stut_index = index;
                if (v_9) {
                    right_index = 0;
                } else {
                    right_index = v_1_1_v_10_v_8;
                }
                stut_right_index = right_index;
                if (v_12) {
                    left_index = (K - 1);
                } else {
                    left_index = v_13_v_11;
                }
                stut_left_index = left_index;
            } else {
                swap = false;
                stut_index = this.last_stut_index;
                stut_right_index = this.last_stut_right_index;
                stut_left_index = this.last_stut_left_index;
            }
            this.last_stut_right_index = stut_right_index;
            this.last_stut_index = stut_index;
            this.last_stut_left_index = stut_left_index;
            if (swap) {
                __node_big_step = true;
                System.arraycopy(this.last_ng, 0, this.last_g, 0, K);
            } else {
                __node_big_step = false;
            }
            v_2 = this.last_g[jeptagon.Pervasives.between(stut_index, K)];
            v_3 = this.last_g[jeptagon.Pervasives.between(stut_left_index, K)];
            v_5 = this.last_g[jeptagon.Pervasives.between(stut_right_index, K)];

            stut_left = v_3.get()[jeptagon.Pervasives.between((N - 1), N)];
            stut_right = v_5.get()[jeptagon.Pervasives.between(0, N)];
            if (swap) {
                for (int i = 0; i<K; i++) {
                    {
                        int[] a_ref_2;
                        a_ref_2 = this.last_g[i].get();
                        System.arraycopy(a_ref_2, 0, y[i], 0, N);
                    }
                } }

            if (this.newone) {
                pppcore.reset(); }
            chunk = pppcore.step(stut_left, stut_right, v_2.get(), this.newone);
            if (this.newone) {

            } else {
                if (((stut_index < K) && (0 <= stut_index))) {
                    this.last_ng[stut_index] = chunk; }
            }
            this.newone = v_7;
        } while(!__node_big_step);
        return y;
    }
    public void reset () {
        this.reset = false;
        this.v_2_1 = 0;
        this.last_stut_right_index = -1;
        this.last_stut_index = -1;
        this.last_stut_left_index = -1;
        for (int i_16 = 0; i_16<K; i_16++) { this.last_g[i_16] = new jeptagon.Pervasives.StaticFuture(FIRST); }
        pppcore.reset();
        this.newone = true;
        for (int i_17 = 0; i_17<K; i_17++) { this.last_ng[i_17] = new jeptagon.Pervasives.StaticFuture(FIRST); }
    }
}
