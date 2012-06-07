package Ac;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;
import jeptagon.AsyncNode;
import jeptagon.AsyncFun;

public class Sim_blocks_ca {
    public static final int default_step_nb_2 = 30000;


    public static void main (String[] args_2) throws java.lang.InterruptedException,
                                              java.util.concurrent.ExecutionException {
        int step_2 = 0;
        if ((args_2.length < 3)) {
            java.lang.System.out.printf("error : not enough arguments.\n");
            return ; }
        int N_2 = Integer.parseInt(args_2[0]);
        int K_2 = Integer.parseInt(args_2[1]);
        int RULE_2 = Integer.parseInt(args_2[2]);
        int[] init = new int[N_2];
        init[(N_2-2)/2] = 1;
        Manual_Ca_pppgame main_2 = new Manual_Ca_pppgame(N_2, K_2, RULE_2, init);
        if ((args_2.length > 3)) {
            step_2 = Integer.parseInt(args_2[3]);
        } else {
            step_2 = default_step_nb_2;
        }
        long t_2 = java.lang.System.currentTimeMillis();
        for (int i_2 = 0; i_2<step_2; i_2++) {
            int[][] ret_2 = main_2.step();
            //java.lang.System.out.printf("=%d> %s\n", i_2, jeptagon.Pervasives.genToString(ret_2));
        }
        java.lang.System.out.printf("time : %d\n", (java.lang.System.currentTimeMillis() - t_2));
        java.lang.System.exit(0);
    }
}
