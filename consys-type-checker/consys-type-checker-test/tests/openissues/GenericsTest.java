package de.tuda.stg.consys.checker.testfiles.openissues;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;

import java.io.Serializable;

public class GenericsTest {
    CassandraStoreBinding replica;
    Ref<@Strong A> obj;
    Ref<@Strong B> objB;

    static class A<T,U> implements Serializable {
        T t;
        U u;
        int n;

        void f() {
        }
    }

    static class B<@Weak T, @Strong U> implements Serializable {
        T t;
        U u;

        int n;

        void f() {
        }
    }

    void testRefInsideTransaction() {
        replica.transaction(ctx -> {
            int n = obj.ref().n;
            @Weak Object t = obj.ref().u;
            @Weak Object u1 = objB.ref().u;
            @Strong Object u2 = objB.ref().t;
            //obj.ref().n = 0;
            //obj.ref().f();
            return Option.empty();
        });
    }
}