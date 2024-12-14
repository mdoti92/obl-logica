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

method {:verify false} UnverifiedPartition(a: array<int>, l: nat, r: nat) returns (index: int){
    var pivot := a[r];
    var i := l - 1;

    for j := l to r + 1
    {
        if a[j] < pivot
        {
            i := i + 1;
            a[i], a[j] := a[j], a[i];
        }
    }
    
    a[i+1], a[r] := a[r], a[i+1];
    return i+1;
}

method {:verify false} UnverifiedQuickSort(a: array<int>, l: nat, r: nat)
{
    if (l < r){
        var pi := UnverifiedPartition(a, l, r);

        UnverifiedQuickSort(a, l, pi - 1);
        UnverifiedQuickSort(a, pi + 1, r);
    }
}


method Partition(a: array<int>, l: int, r: int) returns (index: int)
     modifies a
     requires a.Length > 1
     requires 0 <= l <= r < a.Length
     ensures l <= index <= r
     ensures Preserved(a, l, r)
 {
     var pivot := a[r];
     var i := l - 1;
    
     ghost var original := old(a[l..r]);

     for j := l to r
        invariant l <= j <= r
        invariant l-1 <= i < j
        invariant l <= r < a.Length
        invariant l <= i+1 <= j+1
        invariant Preserved(a, l, r)
     {
         if a[j] < pivot
         {
             i := i + 1;
             a[i], a[j] := a[j], a[i];
             assert multiset(a[l..r]) == multiset(original);
         }
     }
    
     a[i+1], a[r] := a[r], a[i+1];
     assert Preserved(a, l, r);
     return i+1;
}

method QuickSort(a: array<int>, l: int, r: int)
modifies a
requires a.Length > 1
requires 0 <= l <= r < a.Length
ensures Sorted(a, 0, a.Length)
decreases r - l
{
    if (l < r){
        var pi := Partition(a, l, r);

        if l <= pi - 1 {
            QuickSort(a, l, pi - 1);
        }
        if pi + 1 <= r {
            QuickSort(a, pi + 1, r);
        }
    }
}



method {:verify false} TestQuickSort()
{
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 3, 6, 8, 10, 1;

    // Ejecutar QuickSort
    UnverifiedQuickSort(a, 0, a.Length - 1);

    // Imprimir el resultado
    print "Test 1: ", a[..], "\n";

    // Prueba con un arreglo desordenado
    var b := new int[6];
    b[0], b[1], b[2], b[3], b[4], b[5] := 12, 11, 13, 5, 6, 7;
    UnverifiedQuickSort(b, 0, b.Length - 1);
    print "Test 2: ", b[..], "\n";

    // Prueba con un arreglo vacío
    var c := new int[0];
    UnverifiedQuickSort(c, 0, 0);
    print "Test 3 (Empty array): ", c[..], "\n";

    // Prueba con un arreglo de un solo elemento
    var d := new int[1];
    d[0] := 42;
    UnverifiedQuickSort(d, 0, d.Length - 1);
    print "Test 4 (Single element): ", d[..], "\n";

    // Prueba con un arreglo ya ordenado
    var e := new int[5];
    e[0], e[1], e[2], e[3], e[4] := 1, 2, 3, 4, 5;
    UnverifiedQuickSort(e, 0, e.Length - 1);
    print "Test 5 (Already sorted): ", e[..], "\n";

    // Prueba con un arreglo con elementos repetidos
    var f := new int[6];
    f[0], f[1], f[2], f[3], f[4], f[5] := 4, 2, 4, 3, 1, 4;
    UnverifiedQuickSort(f, 0, f.Length - 1);
    print "Test 6 (Duplicates): ", f[..], "\n";
}
