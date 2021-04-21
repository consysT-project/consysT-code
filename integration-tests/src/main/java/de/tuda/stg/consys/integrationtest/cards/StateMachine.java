package de.tuda.stg.consys.integrationtest.cards;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;

import java.util.Set;

public class StateMachine<State> {

    private final Set<State> states;
    private final Set<State> criticalStates;
    private final Set<Transition<State>> transitions;


    private State currentState;

    public StateMachine(Set<State> states, Set<State> criticalStates, Set<Transition<State>> transitions, State initial) {
        if (!states.containsAll(criticalStates))
            throw new IllegalArgumentException("states have to contain all critical states.");

        this.states = states;
        this.criticalStates = criticalStates;
        this.transitions = transitions;
        this.currentState = initial;
    }

    @WeakOp
    public void weakTransition(Transition<State> transition) {
        if (!transitions.contains(transition))
            throw new IllegalArgumentException("transtion has not been defined.");
        if (transition.from != currentState)
            throw new IllegalArgumentException("cannot perform transitions. Wrong state.");
        if (criticalStates.contains(transition.from) || criticalStates.contains(transition.to))
            throw new IllegalArgumentException("weak transition from or to critical state.");

        this.currentState = transition.to;
    }

    @StrongOp
    public void criticalTransition(Transition<State> transition) {
        if (!transitions.contains(transition))
            throw new IllegalArgumentException("transtion has not been defined.");
        if (transition.from != currentState)
            throw new IllegalArgumentException("cannot perform transitions. Wrong state.");
        if (!criticalStates.contains(transition.from) && !criticalStates.contains(transition.to))
            throw new IllegalArgumentException("critical transition does not contain critical state.");

        this.currentState = transition.to;
    }

    /* CARDs decide themself whether to read critical or weak. */
    @WeakOp
    public State weakRead() {
        return currentState;
    }

    @StrongOp
    public State criticalRead() {
        return currentState;
    }

    public static class Transition<T> {
        private final T from;
        private final T to;

        private Transition(T from, T to) {
            this.from = from;
            this.to = to;
        }
    }
}
