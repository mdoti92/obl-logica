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
    requires left <= right - 2
    ensures Preserved(a, left, right)
    ensures forall k: int :: left <= k < index < right ==> a[k] <= a[index] // Todos los elementos a la izquierda del pivote son menores o iguales al pivote.
    ensures forall k: int :: left < index < k < right ==> a[index] <= a[k] // Todos los elementos a la derecha del pivote son mayores o iguales al pivote.

  {
    var pivot := a[right - 1];
    var i := left - 1;

    for j := left to right - 2
    invariant left - 1 <= i < j <= right - 2
    invariant Preserved(a, left, right)
    invariant forall k: int :: left <= k <= i ==> a[k] <= pivot
    invariant forall k: int :: i < k < j ==> a[k] >= pivot
    {
        if a[j] < pivot
        {
            i := i + 1;
            a[i], a[j] := a[j], a[i];
        }
    }
    
    a[i+1], a[right - 1] := a[right - 1], a[i+1];

    return i + 1;
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