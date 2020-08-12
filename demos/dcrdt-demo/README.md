# Implementing Delta-CRDTs in Consys

Consys supports implementing custom Delta-CRDTs, as presented in `Almeida et al. - 2018 - Delta State Replicated Data Types`. 

## Delta-CRDT overview
Delta-CRDTs are an extension of CRDTs, which are a replicated data structure synchronized using a `merge` method, which merges two states into a new one. 

Delta-CRDTs provide the advantage of reduced data transfer, as they are synchronized through _delta-states_. If a replica has changed, it will only need to send a difference. 
Other replicas can incorporate these changes by implementing the `merge` method, which takes a _delta-state_ parameter. 

The structure must implement a _join-semilattice_; Please see the referenced publication for more details on the formal requirements it has to meet.
## Implementing a Delta-CRDT

Contrary to the typical workflow of Consys, using a Delta-CRDT structure requires implementing a custom class defining a `merge` method. Additionally, methods must follow a certain convention to convey whether they result in a delta state. 
Automatically inferring delta states is not currently in scope of this project.

The following exemplifies a DCRDT implementation using an AddOnlySet. 

```
public class AddOnlySetString extends DeltaCRDT implements Serializable {

    private Set<String> set = new HashSet<String>();


    @Override
    public void merge(Object other) {
        if (other instanceof Set) {
            Set<String> s = (Set<String>) other;
            set.addAll(s);
        }
    }

    // adds a new String to this set
    public Delta addElement(String str) {
        set.add(str);
        Set<String> s = new HashSet<String>();
        s.add(str);
        return new Delta(s);
    }

    // adds a new String to this set. 
    // Returns whether the current local set did not yet include this string.
    public ResultWrapper<Boolean> addElement2(String str) {
        boolean result = set.add(str);
        Set<String> s = new HashSet<String>();
        s.add(str);
        return new ResultWrapper<>(result, s);
    }


}
```
The `addElement` method returns a Delta instance containing _delta-state_. 
`merge()` takes an `Object` parameter. Any value wrapped in a `Delta` or `ResultWrapper` instance will be passed here.


Things to note:
* The class must be Serializable. When a replica is initially registered using `replicate()`, it is transmitted to other clients as a whole, without the use of delta states.
* As of yet, akka does not support generics, which is why the merge method only takes an `Object`. This is also why this example explicitly uses strings. 
* If a method results in a changed state, it must return a `Delta` instance that includes the delta state. Akka will transmit this Delta to other replicas by invoking their `merge` method.
* If a method intended to return a value results in a changed state, it must return a `ResultWrapper` object, which allows setting a delta state and an arbitrary value. `ResultWrapper` takes a type parameter, as akka's generics limitation does not apply here.
* Please not that DCRDT methods are currently not yet atomic. This can pose a problem if a set being iterated over is modified by a `merge()` call. This issue will be fixed in a future version.

Once implemented correctly, instances of DCRDT classes can be used just like any other data type in akka:

```
// ...
if (master) {
    set = system().replicate("counter", new AddOnlySetString(), JConsistencyLevels.DCRDT);
} else {
    set = system().lookup("counter", AddOnlySetString.class, JConsistencyLevels.DCRDT);
}

// ...
set.ref().addElement("Hello");

// ...
if (! set.ref().addElement2("Hello").value) {
    System.out.println("element already in set");
}
```