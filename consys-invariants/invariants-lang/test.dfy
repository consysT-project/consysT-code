method Abs(x: int) returns (y: int)
  ensures y == abs(x);
{
  return if x < 0 then -x else x;
}

function abs(x: int): int
{
  if x < 0 then -x else x
}

method MultipleReturns(x: int, y: int) returns (more: int, less: int)
{
  more := x + y;
  less := x - y;
  // comments: are not strictly necessary.
}


method Max(a: int, b: int) returns (c: int)
  ensures c >= b;
  ensures c >= a;
{
  if (a > b) {
    return a;
  } else {
    return b;
  }
}

function method max(a: int, b: int): int
{
    if a < b then b else a
} 

method Testing()
{
  var x := max(42, 23);
  assert x == 42;

  var y := Abs(-42);
  assert y >= 0;
}

function method replicas(): set<int> {
    {23, 42, 322}
}

function method replica(): int 
    ensures replica() in replicas();
{
    42
}


function sum(s: set<int>): int
{
    var v :| v in s; v + (sum(s - { v }))
}



class GCounter {
    var increments: map<int, int>;


    predicate isWellformed()
        reads this; 
    {
        (forall i :: i in increments.Keys ==> increments[i] >= 0) && replicas() == increments.Keys
    }

    

    constructor(incs: map<int, int>)
        requires forall i :: i in incs.Keys ==> incs[i] >= 0;
        requires replicas() == incs.Keys;
        ensures isWellformed();
    {
        this.increments := incs;
    }

    constructor Zero() 
        ensures forall i :: i in increments.Keys ==> increments[i] == 0;
        ensures isWellformed();
    {
        var incs: map<int, int> := map[];

        var rs := replicas(); 

        while (rs != {})
            invariant forall i :: i in incs.Keys ==> incs[i] == 0;
            invariant replicas() == rs + incs.Keys;
            decreases rs;
        {
            var r :| r in rs;
            incs := incs + map[r := 0];
            rs := rs - {r};
        }        
        increments := incs;
    }

    
    method GetValue() returns (result: int)
        requires isWellformed();
        ensures result >= 0;
        ensures result == sum(increments.Values);
    {
        var values := increments.Values;
        var sum := 0;

        while ( values != {} )
            invariant forall v :: v in values ==> v >= 0;
            invariant sum >= 0;
            decreases values;
        {
            var v :| v in values;
            sum := sum + v;
            values := values - { v };
        }

        return sum;
    }


    method Inc(n: int) 
        requires n >= 0;
        requires isWellformed();
        ensures isWellformed();
        modifies this;
    {
        var v := increments[replica()];
        increments := increments + map[replica() := v + n];
    }


    method Merge(other: GCounter) returns (result: GCounter)
        requires isWellformed();
        requires other.isWellformed();
        ensures result.isWellformed();
    {
        var incs: map<int, int> := map[];

        var rs := replicas(); 

        while (rs != {})
            invariant forall i :: i in incs.Keys ==> incs[i] >= 0;
            invariant replicas() == rs + incs.Keys;
            decreases rs;
        {
            var r :| r in rs;
            var thisV := increments[r];
            var otherV := other.increments[r];

            incs := incs + map[r := thisV + otherV];
            rs := rs - {r};
        }        
        return new GCounter(incs);                
    }
}


class Account {
    var deposits: GCounter;
    var withdraws: GCounter;

    predicate isWellformed()
        reads this;
        reads deposits;
        reads withdraws; 
    {
        deposits.isWellformed() && withdraws.isWellformed()
    }

    constructor(deposits: GCounter, withdraws: GCounter) 
        requires deposits.isWellformed();
        requires withdraws.isWellformed();
        ensures isWellformed();
    {
        this.deposits := deposits;
        this.withdraws := withdraws;        
    }

    constructor Zero() 
        ensures isWellformed();
    {
        this.deposits := new GCounter.Zero();
        this.withdraws := new GCounter.Zero();
    }

    method GetValue() returns (result: int)
        ensures result == sum(deposits.increments.Values) - sum(withdraws.increments.Values);
    {
        var plus := deposits.GetValue();
        var minus := withdraws.GetValue();
        return plus - minus;
    }

    method Deposit(n: int)
        requires n >= 0;
        requires isWellformed();
        ensures isWellformed();
        modifies deposits;
    {
        deposits.Inc(n);
    }

    method Withdraw(n: int)
        requires n >= 0;
        requires isWellformed();
        ensures isWellformed();
        modifies withdraws;
    {
        withdraws.Inc(n);
    }

    method Merge(other: Account) returns (result: Account)
        requires isWellformed();
        requires other.isWellformed();
        ensures result.isWellformed();
    {
        var newDeposits := deposits.Merge(other.deposits);
        var newWithdraws := withdraws.Merge(other.withdraws);

        return new Account(newDeposits, newWithdraws);
    }
    

}



method AccountTest(acc1: Account, acc2 : Account) 
    requires acc1.isWellformed();
    requires acc2.isWellformed();
    modifies acc1, acc2, acc1.deposits, acc2.deposits, acc1.withdraws, acc2.withdraws;
{
    var a := acc1;
    var b := acc2;
    
    a.Deposit(500);
    a.Deposit(100);

    b.Deposit(200);

    a := a.Merge(b);
    b := b.Merge(a);




}

