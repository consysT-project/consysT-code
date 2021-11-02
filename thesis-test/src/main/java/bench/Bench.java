package bench;

import java.util.concurrent.Callable;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public interface Bench {
    void setup(int id);
    void operation();
    void shutdown();

    default void doTransaction(Callable<Void> transaction, long msRetry) {
        try {
            transaction.call();
        } catch (Exception e) {
            if (e instanceof TimeoutException) {
                try {
                    TimeUnit.MILLISECONDS.sleep(msRetry);
                } catch (InterruptedException ignored) {}
                doTransaction(transaction, msRetry);
            }
        }
    }
}
