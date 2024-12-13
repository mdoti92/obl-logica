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
    requires a.Length >= 2
    ensures Sorted(a)
  {
    for i := 1 to a.Length
      invariant Ordered(a,0,i)
      invariant Preserved(a,0,a.Length)
    {
      for j := i - 1 downto 0
        invariant j < i
        invariant Ordered(a,0,j)
        invariant Preserved(a,0,a.Length)
      {
        if a[j] > a[j+1] {
          a[j], a[j+1] := a[j+1], a[j];
        }
      }

    }
  }

method TestInsertionSort()
{
  // Caso 1: Arreglo ya ordenado
  var a1 := new int[5] [1, 2, 3, 4, 5];
  InsertionSortSort(a1);
  assert Ordered(a1, 0, a1.Length);

  // Caso 2: Arreglo en orden inverso
  var a2 := new int[5] [5, 4, 3, 2, 1];
  InsertionSortSort(a2);
  assert Ordered(a2, 0, a2.Length);

  // Caso 3: Arreglo parcialmente ordenado
  var a3 := new int[6] [1, 3, 2, 5, 4, 6];
  InsertionSortSort(a3);
  assert Ordered(a3, 0, a3.Length);

  // Caso 4: Arreglo con elementos iguales
  var a4 := new int[4] [2, 2, 2, 2];
  InsertionSortSort(a4);
  assert Ordered(a4, 0, a4.Length);

  // Caso 5: Arreglo vacío (no debe ejecutarse por precondición)
  // El siguiente código fallaría si se descomenta porque viola la precondición.
  // var a5 := new int[0] [];
  // InsertionSortSort(a5);

  // Caso 6: Arreglo con un solo elemento (no debe ejecutarse por precondición)
  // El siguiente código fallaría si se descomenta porque viola la precondición.
  // var a6 := new int[1] [42];
  // InsertionSortSort(a6);
}
