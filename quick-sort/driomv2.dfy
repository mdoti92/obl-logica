method Quicksort(a: array<int>, low: int, high: int)
    requires 0 <= low <= high <= a.Length
    ensures a[..] == old(a[..]).Sorted()
    ensures old(a[..]) == a[..].PermutationOf(old(a[..]))
{
    if low < high {
        var p := Partition(a, low, high);
        Quicksort(a, low, p - 1);
        Quicksort(a, p + 1, high);
    }
}

method Partition(a: array<int>, low: int, high: int) returns (pivotIndex: int)
    requires 0 <= low <= high < a.Length
    modifies a
    ensures low <= pivotIndex <= high
    ensures a[..].PermutationOf(old(a[..]))
    ensures a[low .. pivotIndex] <= a[pivotIndex]
    ensures a[pivotIndex] <= a[pivotIndex + 1 .. high + 1]
{
    var pivot := a[high];
    var i := low - 1;
    for j := low to high - 1
        invariant low <= i < j <= high
        invariant a[..].PermutationOf(old(a[..]))
        invariant forall k :: low <= k <= i ==> a[k] <= pivot
        invariant forall k :: i + 1 <= k < j ==> a[k] > pivot
    {
        if a[j] <= pivot {
            i := i + 1;
            Swap(a, i, j);
        }
    }
    Swap(a, i + 1, high);
    return i + 1;
}

method Swap(a: array<int>, i: int, j: int)
    requires 0 <= i < a.Length && 0 <= j < a.Length
    modifies a
    ensures a[..].PermutationOf(old(a[..]))
{
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
}
