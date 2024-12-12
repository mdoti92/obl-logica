method InsertionSort(A: array<int>)
    requires A.Length > 2
    modifies A
    ensures forall i, j :: 0 <= i < j < A.Length ==> A[i] <= A[j]
{
    var N := A.Length;
    for i := 1 to N
        invariant 0 <= i <= N
        invariant forall x, y :: 0 <= x < y < i ==> A[x] <= A[y]
    {
        var key := A[i];
        var j := i - 1;
        while j >= 0 && A[j] >= key
            invariant -1 <= j < i
            invariant forall x, y :: 0 <= x < y <= i && (x <= j || y > j) ==> A[x] <= A[y]
        {
            A[j + 1] := A[j];
            j := j - 1;
        }
        A[j + 1] := key;
    }
}
