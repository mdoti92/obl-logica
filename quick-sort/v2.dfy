twostate predicate Sorted(a: array<int>, left: int, right: int)
reads a
requires 0 <= left <= right <= a.Length
{
    Ordered(a,left,right) && Preserved(a,left,right)
}
predicate Ordered(a: array<int>, left: nat, right: nat)
reads a
requires left <= right <= a.Length
{
    forall i: nat :: 0 < left <= i < right ==> a[i-1] <= a[i]
}

twostate predicate Preserved(a: array<int>, left: nat, right: nat)
reads a
requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

predicate minimalElement(s: seq<int>, min: int) {
    forall x: int | x in s :: min <= x
}

predicate maximalElement(s: seq<int>, max: int) {
    forall x: int | x in s :: max >= x
}


predicate partitioned(a: seq<int>, from: nat, p: nat, to: nat)
requires 0 <= from <= p < to <= |a|
{
    maximalElement(a[from..p], a[p]) &&
    minimalElement(a[p..to], a[p])
}

twostate predicate permutationSegment(a: array<int>, from: nat, to: nat)
    reads a
    requires a.Length == old(a.Length)
    requires 0 <= from <= to <= a.Length
{
    a[..from] == old(a[..from]) && a[to..] == old(a[to..])// && Preserved(a, from, to)
}


method partition(a: array<int>, from: nat, to: nat) returns (p: nat)
    requires a.Length >= 1
    requires 0 <= from < to <= a.Length
    modifies a
    ensures from <= p < to
    ensures partitioned(a[..], from, p, to)
    ensures Preserved(a, from, to)
{
    var i: int := from - 1;
    var j: nat := from;

    while j < (to - 1)
    invariant from <= i + 1 <= j < to

    invariant maximalElement(a[from..(i + 1)], a[to - 1])
    invariant minimalElement(a[(i + 1)..j], a[to - 1])

    invariant permutationSegment(a, from, to)
    {
        if a[j] <= a[to - 1] {
            i := i + 1;
            a[i], a[j] := a[j], a[i];
        }

        j := j + 1;
    }

    a[i + 1], a[to - 1] := a[to - 1], a[i + 1];

    return i + 1;
}

method QuickSort(a: array<int>, left: int, right: int)
    modifies a
    requires 0 <= left <= right <= a.Length
    ensures Sorted(a, left, right)
    decreases right - left
{    
    if left - right <= 1 {
        return;
    } else {
        var p := partition(a, left, right);
        QuickSort(a, left, p);
        QuickSort(a, p + 1, right);
    }
}