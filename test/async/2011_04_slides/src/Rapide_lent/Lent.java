package Rapide_lent;

public class Lent {
    protected int v_2;
    protected final int N;
    
    public Lent (int N) {
        this.N = N;
        {
            this.v_2 = 1;
        }
    }
    public int step () {
        int y = 0;
        int v = 0;
        y = this.v_2;
        v = (jeptagon.Pervasives.do_stuff(N) + y);
        this.v_2 = v;
        return y;
    }
    public void reset () {
        this.v_2 = 1;
    }
}