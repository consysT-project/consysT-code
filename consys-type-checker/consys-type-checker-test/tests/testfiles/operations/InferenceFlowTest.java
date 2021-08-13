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
        // TODO: resolve field in member select cascade on lhs (but not on rhs)
        boxBox.value.value = box.value; // ok
        boxBox.value = box; // error
        boxBox.value.value = 0; // error
        // TODO: reference problem -> simplest solution: also consider reads of non-primitive fields for inference and checking, if on rhs
        //       only for rhs of assignments, we can still do reads in other contexts
        //       Alternative: if we encounter a field reference type on rhs
        //       Alternative: forbid non-primitive fields on rhs
        if (box.value > 0) {} // ok
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
