package Ac;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;
import jeptagon.AsyncNode;
import jeptagon.AsyncFun;

public class Manual_Ca_pppgame {
    protected Async_factory_pppcore pppcore;
    protected Future<int[]>[] last_g;
    protected Future<int[]>[] last_ng;
    protected int last_stut_index;
    protected int last_stut_left_index;
    protected int last_stut_right_index;
    protected boolean newone;
    protected int v_15;
    protected boolean reset;
    protected int v_2_1;
    protected boolean reset_1;
    protected int v_2_2;
    protected final int N;
    protected final int K;
    protected final int RULE;
    protected final int[] FIRST;

    public Manual_Ca_pppgame (int N, int K, int RULE, int[] FIRST) {
        this.N = N;
        this.K = K;
        this.RULE = RULE;
        this.FIRST = FIRST;
        this.pppcore = new Async_factory_pppcore(3, (K + 1), N, RULE);
        this.last_g = new Future[K];
        this.last_ng = new Future[K];
        {
            this.v_2_2 = 0;
            this.reset_1 = false;
            this.reset = false;
            this.v_2_1 = 0;
            this.v_15 = 0;
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
            int v_1_2 = 0;
            boolean v_17 = true;
            int v_1_1 = 0;
            boolean v_16 = true;
            int v_14 = 0;
            boolean v_12 = true;
            int v_13_v_11 = 0;
            boolean v_9 = true;
            int v_10_v_8 = 0;
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
            int abs_index = 0;
            int offset = 0;
            int v_1999 = 0;
            boolean v_199 = true;
            int mod_index = 0;
            v_7 = !this.newone;
            if (this.newone) {
                if (this.reset_1) {
                    abs_index = 0;
                } else {
                    abs_index = this.v_2_2;
                }
                v = (abs_index == 0);
                swap = v;
                v_17 = (abs_index == (K - 1));
                v_1_2 = (abs_index + 1);
                this.v_2_2 = v_1_2;
                this.reset_1 = v_17;
            } else {
                swap = false;
            }
            if (swap) {
                if (this.reset) {
                    v_14 = 0;
                } else {
                    v_14 = this.v_2_1;
                }
                v_16 = (v_14 == (K - 1));
                this.reset = v_16;
                v_1_1 = (v_14 + 1);
                this.v_2_1 = v_1_1;
                offset = v_14;
                __node_big_step = true;
            } else {
                offset = this.v_15;
                __node_big_step = false;
            }
            this.v_15 = offset;
            if (this.newone) {
                index = (abs_index + offset);
                v_199 = (index > (K - 1));
                v_1999 = (index - K);
                if (v_199) {
                    mod_index = v_1999;
                } else {
                    mod_index = index;
                }
                v_10_v_8 = (mod_index + 1);
                v_9 = (v_10_v_8 > (K - 1));
                v_13_v_11 = (mod_index - 1);
                v_12 = (v_13_v_11 < 0);
                stut_index = mod_index;
                if (v_9) {
                    right_index = 0;
                } else {
                    right_index = v_10_v_8;
                }
                stut_right_index = right_index;
                if (v_12) {
                    left_index = (K - 1);
                } else {
                    left_index = v_13_v_11;
                }
                stut_left_index = left_index;
            } else {
                stut_index = this.last_stut_index;
                stut_right_index = this.last_stut_right_index;
                stut_left_index = this.last_stut_left_index;
            }
            this.last_stut_right_index = stut_right_index;
            this.last_stut_index = stut_index;
            this.last_stut_left_index = stut_left_index;
            if (swap) {
                System.arraycopy(this.last_ng, 0, this.last_g, 0, K);
            } else {

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
        this.v_2_2 = 0;
        this.reset_1 = false;
        this.reset = false;
        this.v_2_1 = 0;
        this.v_15 = 0;
        this.last_stut_right_index = -1;
        this.last_stut_index = -1;
        this.last_stut_left_index = -1;
        for (int i_16 = 0; i_16<K; i_16++) { this.last_g[i_16] = new jeptagon.Pervasives.StaticFuture(FIRST); }
        pppcore.reset();
        this.newone = true;
        for (int i_17 = 0; i_17<K; i_17++) { this.last_ng[i_17] = new jeptagon.Pervasives.StaticFuture(FIRST); }
    }
}
