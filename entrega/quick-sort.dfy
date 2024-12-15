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
    requires a.Length > 1
    requires 0 <= left < right <= a.Length
    requires left <= right - 2
    ensures Preserved(a, left, right)
  {
    var pivot := a[right - 1];
    var i := left - 1;

    for j := left to right - 2
    invariant left - 1 <= i < j <= right - 2
    invariant Preserved(a, left, right)
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
    requires 0 <= left <= right <= a.Length
    ensures Sorted(a)
    decreases right - left
  {
    if left - right <= 0 {
      return;
    }

    var pivot := Partition(a, left, right);

    QuickSort(a, left, pivot);
    QuickSort(a, pivot + 1, right);
  }


  method TestQuickSort() 
{
  // Caso Normal
  var a := new int[11] [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5];
  QuickSort(a, 0, a.Length);
  assert Ordered(a, 0, a.Length);

  // Caso Borde 1: Arreglo vacío
  var b := new int[0];
  QuickSort(b, 0, b.Length);
  assert Ordered(b, 0, b.Length);

  // Caso Borde 2: Un solo elemento
  var c := new int[1] [42];
  QuickSort(c, 0, c.Length);
  assert Ordered(c, 0, c.Length);

  // Caso con elementos repetidos
  var d := new int[5] [5, 5, 5, 5, 5];
  QuickSort(d, 0, d.Length);
  assert Ordered(d, 0, d.Length);

  // Caso ya ordenado
  var e := new int[5] [1, 2, 3, 4, 5];
  QuickSort(e, 0, e.Length);
  assert Ordered(e, 0, e.Length);

  // Caso en orden inverso
  var f := new int[5] [5, 4, 3, 2, 1];
  QuickSort(f, 0, f.Length);
  assert Ordered(f, 0, f.Length);
}
