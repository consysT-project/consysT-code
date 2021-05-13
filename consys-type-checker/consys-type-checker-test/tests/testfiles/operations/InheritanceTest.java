package testfiles.operations;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

import java.io.Serializable;

// TODO: Find a way to get using class (not declaring class) from an identifier expression -> allows overriding with different level. Also needs to keep track of which methods are overridden and which are inherited

// TODO: Find a way to handle case where Derived is processed before Base -> get Tree from Element? -> should only matter if Base is Mixed and not a .class file (in that case it would already have been processed)

// TODO: Find a way to infer when source of base class not available (maybe from TypeElement?) -> is this even possible? if not this would break
// TODO:    -> actually, if Base is not Mixed, we can apply a specified default level to all inherited fields (same as if all operations have a default level)
// TODO:       and if Base is Mixed then the .class file should have annotations on the field declarations
public class InheritanceTest {
    static @Mixed class Base implements Serializable {
        int k;
        int h;

        @WeakOp
        void setK() { k = 0; }

        @StrongOp
        void setH(@Strong int i) {
            h = i;
        }
    }

    static @Mixed class Derived extends Base {
        int j;

        @WeakOp
        void setHDerived() { h = 0; }

        @StrongOp
        void setJfromK() {
            // :: error: assignment.type.incompatible
            j = k;
        }

        @StrongOp
        void setJfromH() {
            // :: error: assignment.type.incompatible
            j = h;
        }
    }
}
