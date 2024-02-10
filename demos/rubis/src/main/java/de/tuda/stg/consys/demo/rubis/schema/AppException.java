package de.tuda.stg.consys.demo.rubis.schema;

public class AppException extends RuntimeException {
    public AppException(String message) {
        super(message);
    }

    public static class NotEnoughCreditsException extends AppException {
        public NotEnoughCreditsException() {
            super("Not enough credits in account to complete transaction.");
        }
    }

    public static class DateException extends AppException {
        public DateException(String msg) {
            super(msg);
        }
    }
}
