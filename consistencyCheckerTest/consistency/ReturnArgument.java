import com.github.allprojects.consistencyTypes.qual.*;

class ReturnArgument {

    @PolyConsistent int identity( @PolyConsistent int number) {return number; }

    void returnArgument() {
        @High int high = 42;
        @Low int low = 42;

        @High int a = identity(high);
        // :: error: (assignment.type.incompatible)
        a = identity(low);

        @Low int b = identity(high);
        b = identity(low);
    }
}