package demos.counter.java;

public class User {
    private Counter counter;

    public User() {
        this.counter = new Counter(0);
    }

    public void click() {
        counter.inc();
    }

    public String updateDisplay() {
        return String.valueOf(counter.get());
    }

    public static void main(String[] args) {
        new User();
    }
}
