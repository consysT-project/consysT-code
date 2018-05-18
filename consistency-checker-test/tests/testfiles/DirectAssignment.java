import com.github.allprojects.consistencyTypes.qual.*;

class DirectAssignment {
    void lowToHigh() {
        @High int a;
        @Low int b = 42;
        // :: error: (assignment.type.incompatible)
        a = b;
    }

    void highToLow() {
        @Low int a;
        @High int b = 42;
        a = b;
    }

    void unannotated() {
        @Low int a;
        @High int b;
        int c = 42;
        a = c;
        // :: error: (assignment.type.incompatible)
        b = c;
    }

    void annotatedInstances(){
        @Low DirectAssignment low = new @High DirectAssignment();
        @High DirectAssignment high = new @High DirectAssignment();

        low = new @Low DirectAssignment();
        // :: error: (assignment.type.incompatible)
        high = new @Low DirectAssignment();
    }
}