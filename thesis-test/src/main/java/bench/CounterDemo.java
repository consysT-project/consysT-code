package bench;

import java.util.Random;

public class CounterDemo {
    public static abstract class CounterBench implements Bench {
        protected final Random random = new Random();

        public void operation() {
            int roll = random.nextInt(100);
            if (roll < 33) {
                writeTransaction();
            } else {
                readTransaction();
            }
        }

        protected abstract void writeTransaction();
        protected abstract void readTransaction();
    }

    public static class Mixed extends CounterBench {
        private demos.counter.consystop.User user;

        public void setup(int id) {
            if (id == 0) {
                user = new demos.counter.consystop.User("127.0.0.1", true);
            } else {
                user = new demos.counter.consystop.User("127.0.0." + (id+1), false);
            }
        }

        public void shutdown() {
            try {
                user.close();
            } catch (Exception ignored) {}
        }

        protected void writeTransaction() {
            user.click();
        }

        protected void readTransaction() {
            user.updateDisplay();
        }
    }

    public static class Mono extends CounterBench {
        private demos.counter.consyst.User user;

        public void setup(int id) {
            if (id == 0) {
                user = new demos.counter.consyst.User("127.0.0.1", true);
            } else {
                user = new demos.counter.consyst.User("127.0.0." + (id+1), false);
            }
        }

        public void shutdown() {
            try {
                user.close();
            } catch (Exception ignored) {}
        }

        protected void writeTransaction() {
            user.click();
        }

        protected void readTransaction() {
            user.updateDisplay();
        }
    }
}
