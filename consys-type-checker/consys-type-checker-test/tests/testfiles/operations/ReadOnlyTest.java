package testfiles.operations;

import de.tuda.stg.consys.annotations.ReadOnly;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.core.store.cassandra.levels.Weak$;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;

public class ReadOnlyTest {
    static class Box implements Serializable {
        int i = 0;
        Box box;

        void set(int i) { this.i = i; }

        @ReadOnly
        int get() { return i; }

        @ReadOnly
        int getNonMutating() {
            int a = 0;
            a = 1;
            a += 1;
            get();
            return i;
        }

        @ReadOnly
        @Transactional
        int getMutating(CassandraTransactionContextBinding ctx, Box p) {
            // :: error: readonly.declaration
            i = 0;
            // :: error: readonly.declaration
            this.i = 1;

            p.getNonMutating();
            p.get();
            // :: error: readonly.declaration
            p.set(0);

            int a;
            a = 0;
            int c = 0;

            // TODO: how to handle constructors?
            // :: error: readonly.declaration
            Box b = new Box();
            // :: error: readonly.declaration
            b.i = 0;

            // :: error: readonly.declaration
            b.box = p;
            // :: error: readonly.declaration
            b.box.i = 0;

            b.getNonMutating();
            // :: error: readonly.declaration
            b.set(0);

            // TODO: replication allowed in ReadOnly methods?
            /*
            Ref<Box> o = ctx.replicate("o", CassandraConsistencyLevels.WEAK, Box.class);
              error: readonly.declaration
            o.ref().i = 0;
            */

            return i;
        }

        // readonly.inference
        int getImplicit() { return i; }
    }

    static class DerivedBox extends Box {
        // :: error: readonly.override
        int get() { return super.i; }

        @Override @ReadOnly
        int getNonMutating() { return i; }
    }

    static @Mixed class A {
        private Box w = new Box();

        @StrongOp
        void f() {
            w.set(0);
        }

        @WeakOp @ReadOnly
        void g() {
            w.get();
        }

        @StrongOp @ReadOnly
        @Strong Box getBox() {
            return w;
        }
    }
}
