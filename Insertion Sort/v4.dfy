  twostate predicate Sorted(a: array<int>)
    reads a
  {
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
  }

  ghost predicate Ordered(a: array<int>, left: nat, right: nat)
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
    requires a.Length >= 2
    ensures Ordered(a,0,a.Length)
  {
    for i := 1 to a.Length
      invariant Ordered(a,0,i)
      invariant Preserved(a,0,a.Length)
    {
      var minValue := a[i];
      var minPos := i;
      for j := i - 1 downto 0
        invariant j < i
      {
        var tmp := a[j];
        a[j] := a[j+1];
        a[j+1] := tmp;
      }

    }
  }