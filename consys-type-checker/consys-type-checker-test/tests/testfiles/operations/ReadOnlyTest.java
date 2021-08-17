package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

public @Mixed class ReadOnlyTest {
    private Box strongBox = new Box();

    @StrongOp
    void set() {
        strongBox.set(0);
    }

    @WeakOp
    void get() {
        strongBox.get();
    }

    @WeakOp
    void test() {
        Box f = strongBox.getOtherBox();
        f.i = 0;
    }

    @StrongOp
    @Strong @Immutable Box getBox() {
        return strongBox;
    }


    static class Box implements Serializable {
        int i = 0;
        Box otherBox;

        @SideEffectFree Box() {}

        void set(int i) { this.i = i; }

        @SideEffectFree
        Box getOtherBox() { return otherBox; }

        @SideEffectFree
        int get() { return i; }

        @SideEffectFree
        int getNonMutating() {
            int a = 0;
            a = 1;
            a += 1;
            get();
            return i;
        }

        @SideEffectFree
        @Transactional
        int getMutating(CassandraTransactionContextBinding ctx, Box p) {
            // :: error: purity.not.sideeffectfree.assign.field
            i = 0;
            // :: error: purity.not.sideeffectfree.assign.field
            this.i = 1;

            p.getNonMutating();
            p.get();
            // :: error: purity.not.sideeffectfree.call
            p.set(0);

            int a;
            a = 0;
            int c = 0;

            // TODO: how to handle constructors?
            // :: error: readonly.declaration
            Box b = new Box();
            // :: error: purity.not.sideeffectfree.assign.field
            b.i = 0;

            // :: error: purity.not.sideeffectfree.assign.field
            b.otherBox = p;
            // :: error: purity.not.sideeffectfree.assign.field
            b.otherBox.i = 0;

            b.getNonMutating();
            // :: error: purity.not.sideeffectfree.call
            b.set(0);

            // :: error: purity.not.sideeffectfree.call
            Ref<Box> o = ctx.replicate("o", CassandraConsistencyLevels.WEAK, Box.class);
            // :: error: purity.not.sideeffectfree.assign.field
            o.ref().i = 0;

            return i;
        }

        // readonly.inference
        int getImplicit() { return i; }
    }

    static class DerivedBox extends Box {
        // :: error: readonly.override
        int get() { return super.i; }

        @Override
        int getNonMutating() { return i; }
    }
}
