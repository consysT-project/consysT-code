import com.github.allprojects.consistencyTypes.qual.*;

class Sanitizing {

    @High int sanitize(int anything) {
        @SuppressWarnings("consistency")
        @High int sanitized = anything;
        return sanitized;
    }

    void testSanitize() {
        @Low int low = 42;
        @High int high = sanitize(low);
    }

}
