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

class GCounter {
    var increments: map<int, int>;

    constructor() 
        ensures forall i :: i in increments.Keys ==> increments[i] == 0;
        ensures replicas() == increments.Keys;
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
        requires forall i :: i in increments.Keys ==> increments[i] >= 0; 
        ensures forall i :: i in increments.Keys ==> increments[i] >= 0;
        ensures result >= 0; 
    {
        var values := increments.Values;
        var sum := 0;

        while ( values != {} )
            invariant sum >= 0;
            decreases values;
        {
            var v :| v in values;
            sum := sum + v;
            values := values - { v };
        }

        return sum;
    }


    method Inc() 
        requires forall i :: i in increments ==> increments[i] >= 0; 
        requires replicas() == increments.Keys;
        ensures forall i :: i in increments ==> increments[i] >= 0;
        ensures replicas() == increments.Keys;
        modifies this;
    {
        var v := increments[replica()];
        increments := increments + map[replica() := v + 1];
    }


    method Merge(other: GCounter) returns (result: GCounter)
        requires forall i :: i in increments ==> increments[i] >= 0; 
        requires replicas() == increments.Keys;
        ensures forall i :: i in increments ==> increments[i] >= 0;
        ensures replicas() == increments.Keys;
    {
        
    }







}


