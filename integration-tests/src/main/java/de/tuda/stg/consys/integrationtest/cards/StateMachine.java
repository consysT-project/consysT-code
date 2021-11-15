package de.tuda.stg.consys.integrationtest.cards;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mutable;

import java.util.Set;

public class StateMachine<State> {

    private final Set<State> states;
    private final Set<State> criticalStates;
    private final Set<Transition<State>> transitions;


    private State currentState;

    public StateMachine(@Mutable Set<State> states, @Mutable Set<State> criticalStates, @Mutable Set<Transition<State>> transitions, State initial) {
        if (!states.containsAll(criticalStates))
            throw new IllegalArgumentException("states have to contain all critical states.");

        this.states = states;
        this.criticalStates = criticalStates;
        this.transitions = transitions;
        this.currentState = initial;
    }

    @WeakOp
    @SuppressWarnings("consistency") //TODO: Fix the type system here
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
    @SuppressWarnings("consistency") //TODO: Fix the type system here
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

}
