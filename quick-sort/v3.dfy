  twostate predicate Sorted(a: array<int>)
    reads a
  {
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
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

  method Partition(a: array<int>, left: int, right: int) returns (index: int)
    modifies a
    requires a.Length > 1 // Que pasa cuando esta vacio o es de length = 1
    requires 0 <= left < right <= a.Length
  {
    var pivot := a[right - 1];
    var j := right - 2;
    var i := left;
    while i < j
    invariant left <= i < j < right - 1
    {
        if a[i] <= pivot && a[j] >= pivot
        {
            i := i + 1;
            j := j - 1;
        } else if a[i] > pivot && a[j] >= pivot
        {
            j := j - 1;
        } else if a[i] <= pivot && a[j] < pivot
        {
            i := i + 1;
        } else if a[i] > pivot && a[j] < pivot
        {
            a[i], a[j] := a[j], a[i];
            i := i + 1;
            j := j - 1;
        }
    }

    a[j], a[right - 1] := a[right - 1], a[j];

    return j;
  }

  method QuickSort(a: array<int>, left: int, right: int)
    modifies a
    requires 0 <= left <= right <= a.Length // Ojo que si left == right == a.Length
    ensures Sorted(a)
  {
    if left - right <= 0 {
      return;
    }

    var pivot := Partition(a, left, right);

    QuickSort(a, left, pivot);
    QuickSort(a, pivot + 1, right);
  }