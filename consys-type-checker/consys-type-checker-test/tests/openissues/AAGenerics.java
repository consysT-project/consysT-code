package openissues;

import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

public class AAGenerics {
    static class Pair<E1, E2> {
        @Mutable E1 first;
        @Mutable E2 second;

        @WeakOp
        void write1(@Mutable @Local E1 v) {
            first = null;
        }

        @StrongOp
        void write2(@Mutable @Local E2 v) {
            second = null;
        }
    }
    static class A {}
    static class B extends A {}

    void test1(Ref<@Strong Pair<Integer, Integer>> obj1,
              Ref<@Weak Pair<Integer, Integer>> obj2) {
        obj2 = obj1;
    }

    void test2(Ref<@Strong Pair<@Weak Integer, @Strong Integer>> obj1,
              Ref<@Weak Pair<@Strong Integer, @Weak Integer>> obj2) {
        obj2 = obj1;
    }

    void test3(@Strong Pair<@Weak Integer, @Strong Integer> obj1,
               @Weak Pair<@Strong Integer, @Weak Integer> obj2) {
        obj2 = obj1;
    }

    void test4(@Strong Pair<@Weak Ref<@Weak Integer>, @Weak Ref<@Weak Integer>> obj1,
               @Strong Pair<@Strong Ref<@Strong Integer>, @Strong Ref<@Strong Integer>> obj2) {
        obj2 = obj1;
        obj1 = obj2;
    }

    void test5() {
        Pair<@Immutable @Weak Integer, Integer> p1 = null;
        Pair<@Immutable @Strong Integer, Integer> p2 = null;

        p1 = p2;
    }

    void test6() {
        Pair<? extends @Immutable @Weak A, Integer> p1 = null;
        Pair<? extends @Immutable @Strong B, Integer> p2 = null;

        p1 = p2;
    }
}
