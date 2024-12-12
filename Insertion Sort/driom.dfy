predicate sorted (a: array<int>)
  requires a.Length > 1
	reads a
{
	sortedToIndex(a, (a.Length - 1))
}

predicate sortedToIndex (a: array<int>, i: int)
  requires a.Length > 1
	requires 0 <= i < a.Length
	reads a
{
	forall k :: 0 < k <= i ==> a[k-1] <= a[k]
}

predicate sortedFromIndex (a: array<int>, i: int)
  requires a.Length > 1
	requires 0 <= i < a.Length
	reads a
{
	forall k :: 0 < i < k < a.Length ==> a[k - 1] <= a[k]
}

predicate sortedBetweenIndexs (a: array<int>, j: int, i: int)
  requires a.Length > 1
	requires 0 <= j < i < a.Length
	reads a
{
	forall k :: 0 <= j < k <= i ==> a[k - 1] <= a[k]
}

lemma sortedSeqSubsequenceSorted(a:array<int>, min:int, max:int)
requires a.Length > 1
requires 0 <= min < max < a.Length
//requires sorted(a) // revisar seguramente sacar
ensures sortedBetweenIndexs(a, min, max)
{ }

method swap(a: array<int>, i:int, j:int)
  modifies a
  requires a.Length > 1
  requires 0 <= i < j < a.Length
  requires i + 1 == j
  ensures a[..i] == old(a[..i]) // Revisar
  ensures a[j+1..] == old(a[j+1..])
  ensures a[j] == old(a[i])
  ensures a[i] == old(a[j])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
   var tmp := a[i];
   a[i] := a[j];
   a[j] := tmp;  
} 

method InsertionSort(A: array<int>)
    requires A.Length >= 2
    modifies A
    ensures sorted(A)
{
    var N := A.Length;
    for i := 1 to (N - 1)
        invariant 1 <= i < N
        invariant sortedToIndex(A, i)
        invariant multiset(A[..]) == multiset(old(A[..]))
    {
        var key := A[i];
        var j := i - 1;

        ghost var A' := A;
        while j >= 0 && A[j] > key
            invariant 0 <= j < i
            invariant multiset(A[..]) == multiset(old(A[..]))
            invariant multiset(A[..]) == multiset(A'[..])
            invariant A'[0 .. j] == A[0 .. j]
            invariant A[j+1] == key == A'[i]
            invariant sortedToIndex(A, j)
            invariant sortedBetweenIndexs(A, j+1, i)
            invariant forall k :: j+1 < k <= i ==> key <= A[k]
        {       
            ghost var A'' := A;     
            swap(A, j, j+1);
            assert A[0..j-1] == A''[0..j-1]; // sacar
            assert A[0..j] == A'[0..j]; // sacar
            assert A[j] == A''[j+1] == A'[i] == key;
            assert A[j+2..] == A''[j+2..];
            assert A[j+2..i+1] == A''[j+2..i+1] == A'[j+1..i]; // chequearlo

            j := j - 1;
            sortedSeqSubsequenceSorted(A', j+1, i);
            assert sortedBetweenIndexs(A', j+1, i);
            assert A[j+2 .. i+1] == A'[j+1 .. i];
            assert sortedBetweenIndexs(A, j+2, i+1);
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

method TestSortedFromIndex() {
  var a := new int[5] [1, 2, 3, 4, 5];
  assert sortedFromIndex(a, 2); // Check if the last 3 elements are sorted
}

method TestSortedBetweenIndexs() {
  var a := new int[5] [1, 2, 3, 4, 5];
  assert sortedBetweenIndexs(a, 1, 3); // Check if elements from index 2 to 3 are sorted
}