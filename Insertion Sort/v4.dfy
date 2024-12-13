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
    method InsertionSortSort(a: array<int>)
    modifies a
    ensures Sorted(a)
  {
    for i := 1 to a.Length
      invariant Ordered(a,0,i)
      invariant Preserved(a,0,a.Length)
    {
      var minValue := a[i];
      var minPos := i;
      for j := i - 1 to 0
        invariant j < i
      {
        var tmp := a[j];
        a[j] := a[j+1];
        a[j+1] := tmp;
      }

    }
  }