package de.tuda.stg.consys.integrationtest.cards;

/**
 * Created on 23.06.21.
 *
 * @author Mirko Köhler
 */
public class Transition<T> {
    public final T from;
    public final T to;

    public Transition(T from, T to) {
        this.from = from;
        this.to = to;
    }


}
