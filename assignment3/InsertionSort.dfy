// State Space
datatype StateSpace = StateSpace(a:array<int>, i:nat)

predicate sorted(a: array<int>, l: int, r: int)
reads a
requires a.Length > 0
{
    forall i, j :: 0 <= l <= i < j <= r < a.Length ==> a[i] <= a[j]
}

predicate divided(a: array<int>, j: int, i: int)
reads a
requires a.Length > 0
requires j < a.Length && i < a.Length
{
    forall x, y :: 0 <= x <= j + 1 && j + 2 <= y <= i ==> a[x] <= a[y]
}

method transit(start : StateSpace) returns (final:StateSpace)
modifies start.a
requires start.a.Length > 0
requires start.i == 1
ensures final.a.Length > 0
ensures multiset(start.a[..]) == multiset(final.a[..])
ensures sorted(final.a, 0, final.a.Length - 1)
ensures final.i == start.a.Length
{
    var i := start.i;
    while (i < start.a.Length)
    decreases start.a.Length - i
    invariant 1 <= i <= start.a.Length
    invariant sorted(start.a, 0, i - 1)
    {
        var j := i;
        while (j >= 1 && start.a[j] < start.a[j - 1])
        decreases j
        invariant 0 <= j <= i
        invariant divided(start.a, j-1, i)
        invariant sorted(start.a, 0, j-1)
        invariant sorted(start.a, j + 1, i)
        {
            start.a[j], start.a[j - 1] := start.a[j - 1], start.a[j];
            j := j - 1;
        }
        i := i + 1;
    }
    final := StateSpace(start.a,i);
    assert sorted(final.a,0,final.a.Length-1);
}

//Rho function
function method rho(a: array<int>): StateSpace
{
    StateSpace(a,1)
}

//View Function
function method pi(s: StateSpace): array<int>
{
    s.a
}

method Main()
{
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 89, 43, 57, 21, 73;
    var start := rho(a);
    var final := transit(start);
    var sorted_array := pi(final);
    assert sorted(sorted_array, 0, sorted_array.Length - 1);
}