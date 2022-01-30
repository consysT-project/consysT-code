package de.tuda.stg.consys.demo.rubis;

public class AppException extends RuntimeException {
    public AppException(String message) {
        super(message);
    }
}

class NotEnoughCreditsException extends RuntimeException {
    NotEnoughCreditsException() {
        super("Not enough credits in account to complete transaction.");
    }
}
