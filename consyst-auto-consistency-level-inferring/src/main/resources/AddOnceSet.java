// What is the invariant?
class AddOnceSet<T> {
    Set<T> adds = Sets.newHashset();
    Set<T> removes = Sets.newHashset();

    /*
    ensures \exists int i: \new(adds)[i] == elem
    ensures \forall int i: \new(adds)[i] != elem
                ==> \old(adds)[i] == \new(adds)[i]
    ensures \forall int i: \old(removes)[i] == \new(removes)[i]
     */
    void add(T elem) {
        adds.add(elem);
    }

    /*
    ensures \exists int i: removes[i] == elem
                    && \not_changed(removes, {i})
    ensures not_changed(removes);
    ensures not_changed(adds);
     */
    void remove(T elem) {
        removes.add(elem);
    }

    /*
    pure ==> forall Vars in AddOnceSet: \ensures not_changed(Var)
     */
    boolean /* pure */ contains(T elem) {
        return adds.contains(elem) && !removes.contains(elem);
    }

    /*
    ensures \new(adds) == UNION(\old(adds), \other(adds))
    ensures \new(removes) == UNION(\old(adds), \other(adds))
     */
    RemoveOnceSet<T> merge(RemoveOnceSet<T> other) {
        return new RemoveOneSet(
                Sets.union(adds, other.adds),
                Sets.union(removes, other.removes)
        );
    }
}