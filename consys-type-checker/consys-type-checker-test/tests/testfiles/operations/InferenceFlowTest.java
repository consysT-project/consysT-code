package testfiles.operations;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

public @Mixed class InferenceFlowTest {
    private @Strong Box<Integer> box;
    private @Weak Box<Box<Integer>> boxBox;

    @WeakOp void test() {
        boxBox.value.value = box.value; // ok, primitive assignment
        // :: error: assignment.type.incompatible
        boxBox.value = box; // error, assignment: @Mutable @Weak <- @Mutable @Strong
        boxBox.value.value = 0; // ok, primitive assignment
    }

    @WeakOp Box<Box<Integer>> test2(Box<Box<Integer>> param) {
        param.value = box; // TODO: disallow reference fields to leave the class OR consider them public
        Box<Integer> local = new Box<>();
        param.value = local;
        //local.value = box;
        return param;
    }

    @StrongOp void test1() {
        box.value = 0;
    }
}

class Box<T> {
    T value;
}
