import de.tuda.stg.consys.annotations.invariants.DataModel;

@DataModel public class Player {

    private final String name;
    private int budget = 0;

    public Player(String name) {
        this.name = name;
    }

    //@ assignable \nothing;
    public int getBudget() {
        return budget;
    }

    public void incBudget(int amount) {
        budget += amount;
    }
}
