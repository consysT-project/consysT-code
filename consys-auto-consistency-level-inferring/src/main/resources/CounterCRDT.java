// overkill version
public class CounterCRDT {
    public static final int numOfReplicas = 10;
    public static final int replicaId = 5;

    int[] incs = new int[numOfReplicas];
    int[] decs = new int[numOfReplicas];

    //@ public invariant getValue() >= 0;
    //@ public invariant incs != null && decs != null;

    /*@
      @ requires replicaId >= 0 && replicaId < incs.length;
      @ assignable incs[replicaId];
      @ ensures incs[replicaId] == \old(incs[replicaId]) + 1;
      @*/
    void inc() {
        incs[replicaId] = incs[replicaId] + 1;
    }

    /*@
    @ assignable decs[replicaId];
    @ requires getValue() >= 1;
    @ requires replicaId >= 0 && replicaId < decs.length;
    @ ensures decs[replicaId] == \old(decs[replicaId]) + 1;
    @*/
    void dec() {
        if (getValue() >= 1) decs[replicaId] = decs[replicaId] + 1;
    }


    /*@ assignable incs, decs;
    @
    @ ensures (sumArray(other.incs) > sumArray(incs) ==> incs == other.incs);
    @ ensures (sumArray(other.decs) > sumArray(decs) ==> decs == other.decs);
    @*/
    CounterCRDT merge(CounterCRDT other) {
        return pureMerge(this, other);
    }

    /*************************    Pure Methods    *****************************/
  
  /*@
  @ ensures \result == sumArray(incs) - sumArray(decs);
  @*/
    int /*@ pure @*/ getValue() {
        return sumArray(incs) - sumArray(decs);
    }

    /*@
      @ public normal_behavior
      @ requires arr != null;
      @ assignable \nothing;
      @ requires (\sum int j; 0<=j && j<arr.length; arr[j]) <= Integer.MAX_VALUE;
      @ requires (\sum int j; 0<=j && j<arr.length; arr[j]) >= Integer.MIN_VALUE;
      @ ensures \result == (\sum int j; 0<=j && j<arr.length; arr[j]);
      @
      @*/
    int /*@ pure @*/ sumArray(int[] arr) {
        int sum = 0;
    /*@
      @ maintaining 0 <= i && i <= arr.length;
      @ maintaining sum == (\sum int j; i<=j && 0<=j && j<arr.length; arr[j]);
      @ decreasing arr.length-i;
      @*/
        for (int i = 0; i < arr.length; i++) {
            sum += arr[i];
        }
        return sum;
    }


    /*@
      @ public normal_behavior
      @ requires other != null;
      @ ensures !(other instanceof CounterCRDT) ==> !\result;
      @ ensures (\exists int i; 0<=i && i<incs.length;
      @ incs[i] != ((CounterCRDT) other).incs[i] || decs[i] != ((CounterCRDT) other).decs[i])
      @ ==> !\result;
      @*/
    public boolean /*@ pure @*/ equals(Object other) {
        if (!(other instanceof CounterCRDT)) return false;
        else {
    /*@
      @ maintaining 0 <= i && i <= incs.length;
      @ decreasing incs.length-i;
      @*/
            for (int i = 0; i < incs.length; i++) {
                if (! (incs[i] == ((CounterCRDT) other).incs[i])
                        || !(decs[i] == ((CounterCRDT) other).decs[i])) {
                    return false;
                }
            }
            return true;
        }
    }

    /*@
      @ requires true;
      @
      @ ensures (sumArray(\old(one.incs)) > sumArray(\old(other.incs))) ==> \result.incs == one.incs;
      @ ensures (sumArray(\old(one.decs)) > sumArray(\old(other.decs))) ==> \result.incs == one.decs;
      @ ensures (sumArray(\old(other.incs)) > \old(sumArray(one.incs))) ==> \result.incs == other.incs;
      @ ensures (sumArray(\old(other.decs)) > \old(sumArray(one.decs))) ==> \result.incs == other.decs;
      @
      @ ensures \old(one).equals(\old(other)) ==> one.equals(\result) && other.equals(\result);
      @ ensures (pureMerge(\old(one), \old(other))).equals(pureMerge(\old(other), \old(one)));
      @ ensures (pureMerge(\old(this), pureMerge(\old(one), \old(other)))).equals(pureMerge(pureMerge(\old(this), \old(one)), \old(other)));
      @*/
    CounterCRDT /*@ pure @*/pureMerge(CounterCRDT one, CounterCRDT other) {
        int[] incs;
        int[] decs;
        CounterCRDT merge = new CounterCRDT();
        if(sumArray(one.incs) > sumArray(other.incs)) {
            incs = one.incs;
        }
        else {
            incs = other.incs;
        }
        if(sumArray(one.decs) > sumArray(other.decs)) {
            decs = one.decs;
        } else {
            decs = other.decs;
        }
        merge.incs = incs;
        merge.decs = decs;
        return merge;
    }

    public static void main(String[] args) {
     System.out.println("Done!");
    }


}
