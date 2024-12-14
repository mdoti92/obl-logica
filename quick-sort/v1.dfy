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

method QuickSort(a: array<int>, left: int, right: int)
    modifies a
    requires 0 <= left <= right <= a.Length
    ensures Sorted(a, left, right)
{
    if left < right { 
        var pivot := a[left];
        var i := left;
        var j := right;
        while i <= j 
        invariant left <= i <= right + 1
        invariant left - 1 <= j <= right
        invariant Preserved(a, left, right)
        {
            while a[j] > pivot 
            {
                j := j - 1;
            }
            if i <= j {
                a[i], a[j] := a[j], a[i];
                i := i + 1;
                j := j - 1;
            }
        }
        QuickSort(a, left, j);
        QuickSort(a, i, right);
    }
}

