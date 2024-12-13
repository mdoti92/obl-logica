predicate sorted (a: array<int>)
  requires a.Length >= 0
  reads a
{
	forall k :: 0 < k < a.Length ==> a[k-1] <= a[k]
}

predicate sortedToIndex (a: array<int>, i: int)
  requires a.Length >= 0
  requires -1 <= i < a.Length
  reads a
{
	i < 0 || forall k :: 0 < k <= i ==> a[k-1] <= a[k]
}

predicate sortedFromIndex (a: array<int>, i: int)
  requires a.Length >= 0
	requires 0 <= i < a.Length
	reads a
{
	forall k :: 0 < i < k < a.Length ==> a[k - 1] <= a[k]
}

predicate sortedBetweenIndexs (a: array<int>, j: int, i: int)
  requires a.Length >= 0
  requires 0 <= j <= i < a.Length
  reads a
{
	j == i || forall k :: 0 <= j < k <= i ==> a[k - 1] <= a[k]
}

lemma sortedSubArray(a:array<int>, min:int, max:int)
    requires a.Length > 1
    requires 0 <= min < max < a.Length
    requires sorted(a)
    ensures sortedBetweenIndexs(a, min, max)
{ }

method CopyArray(A: array<int>) returns (A': array<int>)
    requires A.Length > 0
    ensures A'.Length == A.Length
    ensures forall i :: 0 <= i < A.Length ==> A'[i] == A[i]
    ensures A' != A
{    
    var B := new int[A.Length];
    
    for i := 0 to A.Length - 1
        invariant 0 <= i < A.Length
        invariant forall j :: 0 <= j < i ==> B[j] == A[j]
    {
        B[i] := A[i];
        assert B[i] == A[i];
    }

    // Asegurar que la copia es fiel
    assert forall i :: 0 <= i < A.Length ==> B[i] == A[i];
    assert B.Length == A.Length;

    // Asignar la copia a la variable de retorno
    A' := B;
}

  twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
  {
    multiset(a[left..right]) == multiset(old(a[left..right]))
  }

  ghost predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
  {
    forall i: nat :: 0 < left <= i < right ==> a[i-1] <= a[i]
  }

method swap(a: array<int>, j:int, i:int)
  modifies a
  requires a.Length > 1
  requires 0 <= j < i < a.Length
  requires j + 1 == i
  ensures a[..j] == old(a[..j])
  ensures a[i+1..] == old(a[i+1..])
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
   var tmp := a[i];
   a[i] := a[j];
   a[j] := tmp;

   assert a[j] == old(a[i]);
   assert a[i] == old(a[j]);
} 

method InsertionSort(A: array<int>)
    requires A.Length >= 2
    modifies A
    ensures Ordered(A, 0, A.Length)
{
    var N := A.Length;
    for i := 1 to (N - 1)
        invariant 1 <= i < N
        invariant Ordered(A, 0, i)
        invariant Preserved(A, 0, N)
    {
        var key := A[i];
        var j := i - 1;

        ghost var A' := A;
        while j >= 0 && A[j] > key
            invariant -1 <= j < i
        {       
            var tmp := A[j];
            A[j] := A[j+1];
            A[j+1] := tmp;

            assert A[j] <= A[j+1];

            j := j - 1;
        }
    }
}


method TestSorted() {
  var a := new int[5] [1, 2, 3, 4, 5];
  assert sorted(a);
}

method TestSortedToIndex() {
  var a := new int[5] [1, 2, 3, 4, 5];
  assert sortedToIndex(a, 3); // Check if the first 4 elements are sorted
}

method TestSortedToIndexNegativeIndex() {
  var a := new int[5] [1, 2, 3, 4, 5];
  assert sortedToIndex(a, -1); // Check if the first 4 elements are sorted
}

method TestSortedFromIndex() {
  var a := new int[5] [1, 2, 3, 4, 5];
  assert sortedFromIndex(a, 2); // Check if the last 3 elements are sorted
}

method TestSortedBetweenIndexs() {
  var a := new int[5] [1, 2, 3, 4, 5];
  assert sortedBetweenIndexs(a, 1, 3); // Check if elements from index 2 to 3 are sorted
}

method TestSortedBetweenIndexsSameIndex() {
  var a := new int[5] [1, 2, 3, 4, 5];
  assert sortedBetweenIndexs(a, 1, 1); // Check if elements from index 2 to 3 are sorted
}

method TestSwap() {
  var a := new int[5] [1, 3, 2, 4, 5];
  swap(a, 1, 2);
  assert a[1] == 2;
  assert a[2] == 3;
  assert sorted(a);
}

method TestSwapGhost() {
  var a := new int[5] [1, 3, 2, 4, 5];
  ghost var a'' := a;
  swap(a, 1, 2);
  assert a[1] == a''[2];
  assert a[1] == 2;
  assert a[2] == 3;
  assert sorted(a);
}