package testfiles.operations.example;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;

// TODO: operation invocation in implicit context

// non-mixed base class
public abstract class BankAccount {
    // adding Mixed to a class at a type use location instead of at a declaration
    Ref<@Mixed User> owner;
    // not written to in base class -> Local in base and derived contexts
    int value;

    // we need to annotate these arguments with the strongest level we may wish to use in a derived class
    //      -> TODO: problematic for unannotated classes, where these are Inconsistent
    abstract void deposit(@Strong int amount);
    abstract void withdraw(@Strong int amount);

    abstract boolean isActivated();

    // returns a Weak value when class is Weakly defaulted
    //      -> derived classes can override to provide a Strong implementation, which can be accessed through casting
    //         the result of a .ref() call
    int getBalance() {
        return value;
    }

    @Transactional
    String printReport() {
        // read-level refinement (for field 'value')
        return owner.ref().getName() + owner.ref().getAddress() + value;
    }

    // Operation method in non-mixed class
    @StrongOp
    void transferOwnership(Ref<@Mixed User> user) {
        // the new user must also be Mixed, but can be Mixed(Strong) or Mixed(Weak)
        this.owner = user;
    }
}

@Mixed class PrepaidAccount extends BankAccount {
    @StrongOp
    void deposit(@Strong int amount) {
        value += amount;
    }

    @StrongOp
    void withdraw(@Strong int amount) {
        if (value >= amount) {
            value -= amount;
        } else {
            throw new IllegalArgumentException();
        }
    }

    @StrongOp
    boolean isActivated() {
        return true; // placeholder for some business logic
    }

    @Override
    @StrongOp
    int getBalance() {
        return value;
    }
}

// maybe just show declaration, since implementation offers no new features
@Mixed class OverdraftAccount extends BankAccount {
    int overdraftLimit;

    @StrongOp
    void deposit(@Strong int amount) {
        value += amount;
    }

    @StrongOp
    void withdraw(@Strong int amount) {
        value -= amount;
    }

    @StrongOp
    boolean isActivated() {
        return true; // placeholder for some business logic
    }

    @Override
    @StrongOp
    int getBalance() {
        return value;
    }
}

class User {
    // final field is Local
    final String name;
    // address can be Strong or Weak depending on instantiation as Mixed(Strong) or Mixed(Weak)
    String address;

    // constructors are neither StrongOp or WeakOp, writes are considered Local
    User(String name, String address) {
        this.name = name;
        this.address = address;
    }

    // TODO: Problem with argument default levels
    void changeAddress(String address) {
        this.address = address;
    }

    String getName() {
        return name;
    }

    String getAddress() {
        return address;
    }
}

class Bank {
    private final CassandraStoreBinding store;

    Bank(CassandraStoreBinding store) {
        this.store = store;
    }

    void transfer(Ref<@Mixed BankAccount> sender, Ref<@Mixed BankAccount> receiver, @Strong int amount) {
        store.transaction(tx -> {
            // Strong implicit context allows execution of StrongOp methods
            //      -> TODO: base.isActivated must explicitly return a Strong value for context to be Strong
            if (sender.ref().isActivated() && receiver.ref().isActivated()) {
                sender.ref().withdraw(amount);
                receiver.ref().deposit(amount);
            }
            return Option.empty();
        });
    }
}
