package Ac;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;
import jeptagon.AsyncNode;
import jeptagon.AsyncFun;

public class Manual_Game {
    protected boolean reset;
    protected int v_2;
    protected int[] v_4;
    protected boolean v_1_4_v_1_1;
    protected int v_3_3_v_3_1;
    protected int x_2_v_6;
    protected int x_1;
    protected int[] yc;
    protected final int N;
    protected final int RULE;
    protected final int[] FIRST;
    
    public Manual_Game (int N, int RULE, int[] FIRST) {
        this.N = N;
        this.RULE = RULE;
        this.FIRST = FIRST;
        this.v_4 = new int[(N + 2)];
        this.yc = new int[(N + 2)];
        {
            this.v_2 = 0;
            this.reset = false;
            this.x_1 = CONSTANTES.NULL_CS;
            this.v_1_4_v_1_1 = false;
            this.v_3_3_v_3_1 = 0;
            for (int i_18 = 0; i_18<(N + 2); i_18++) { this.v_4[i_18] = 0; }
            this.x_2_v_6 = CONSTANTES.NULL_CS;
            for (int i_19 = 0; i_19<(N + 2); i_19++) { this.yc[i_19] = FIRST[i_19]; }
        }
    }
    public int[] step () throws java.lang.InterruptedException, java.util.concurrent.ExecutionException {
        int[] y = new int[(N + 2)];
        boolean __node_big_step = true;
        do {
            boolean ck_1 = true;
            boolean ck = true;
            int v_9 = 0;
            boolean v_8 = true;
            int v_4_1 = 0;
            int v_3_2 = 0;
            int v_2_2 = 0;
            int v_1_2 = 0;
            int v_7 = 0;
            int nb = 0;
            int v_2_3_v_2_1 = 0;
            boolean v_10_v_5 = true;
            boolean reset_2_reset_1 = true;
            int index_cpt_2 = 0;
            int v_1 = 0;
            boolean v_3 = true;
            int v = 0;
            boolean begin = true;
            int x_l = 0;
            int y_l = 0;
            if (this.reset) {
                v = 0;
            } else {
                v = this.v_2;
            }
            v_1 = (v + 1);
            this.v_2 = v_1;
            v_3 = (v == ((N + 2) - 1));
            begin = (v == 0);
            this.reset = v_3;
            v_2_2 = (this.x_1 << 2);
            this.x_1 = this.x_2_v_6;
            v_3_2 = (this.x_2_v_6 << 1);
            v_4_1 = (v_2_2 | v_3_2);
            reset_2_reset_1 = (begin || this.v_1_4_v_1_1);
            if (reset_2_reset_1) {
                index_cpt_2 = 0;
            } else {
                index_cpt_2 = this.v_3_3_v_3_1;
            }
            ck = (index_cpt_2 == 2);
            v_10_v_5 = (index_cpt_2 == ((N + 2) - 1));
            v_9 = (index_cpt_2 - 1);
            this.v_1_4_v_1_1 = v_10_v_5;
            v_2_3_v_2_1 = (index_cpt_2 + 1);
            this.v_3_3_v_3_1 = v_2_3_v_2_1;
            if (ck) {
                
            } else {
                ck_1 = (index_cpt_2 == (N + 1));
            }
            if (begin) {
                __node_big_step = true;
                for (int i_1 = 0; i_1<(N + 2); i_1++) { y[i_1] = this.yc[i_1]; }
                for (int i_2 = 0; i_2<(N + 2); i_2++) { this.v_4[i_2] = y[i_2]; }
            } else {
                __node_big_step = false;
            }
            x_l = this.v_4[jeptagon.Pervasives.between(index_cpt_2, (N + 2))];
            nb = (v_4_1 | x_l);
            this.x_2_v_6 = x_l;
            v_7 = (1 << nb);
            v_1_2 = (RULE & v_7);
            v_8 = (v_1_2 == 0);
            if (v_8) {
                y_l = 0;
            } else {
                y_l = 1;
            }
            if (ck) {
                if ((((N + 1) < (N + 2)) && (0 <= (N + 1)))) {
                    this.yc[(N + 1)] = y_l; }
            } else {
                if (ck_1) {
                    if (((0 < (N + 2)) && (0 <= 0))) {
                        this.yc[0] = y_l; }
                } else {
                    
                }
            }
            if (((v_9 < (N + 2)) && (0 <= v_9))) {
                this.yc[v_9] = y_l; }
        } while(!__node_big_step);
        return y;
    }
    public void reset () {
        this.v_2 = 0;
        this.reset = false;
        this.x_1 = CONSTANTES.NULL_CS;
        this.v_1_4_v_1_1 = false;
        this.v_3_3_v_3_1 = 0;
        for (int i_18 = 0; i_18<(N + 2); i_18++) { this.v_4[i_18] = 0; }
        this.x_2_v_6 = CONSTANTES.NULL_CS;
        for (int i_19 = 0; i_19<(N + 2); i_19++) { this.yc[i_19] = FIRST[i_19]; }
    }
}
