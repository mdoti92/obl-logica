method max_profit (a : array<int>) returns (l : nat, r: nat)
requires a.Length > 2
ensures 0 <= l < r < a.Length
ensures forall l', r' :: 0 <= l' < r' < a.Length ==> a[r'] - a[l']  <= a[r] - a[l]
{
    var i : nat, imin : nat, profit : int;
    i, l, r, imin, profit := 2, 0, 1, if a[0] < a[1] then 0 else 1, a[1] - a[0] ;
    while (i < a.Length)
        invariant 0 <= l < r < a.Length
        invariant 2 <= i <= a.Length
        invariant 0 <= imin < i
        invariant profit == a[r] - a[l]
        invariant forall l', r' :: 0 <= l' < r' < i ==> a[r'] - a[l']  <= profit
        invariant forall j :: 0 <= j < i ==> a[imin] <= a[j]
        {
            var profit' := a[i] - a[imin];
            if profit' > profit {l, r, profit := imin, i, profit' ;}
            if a[i] < a[imin] {imin := i;}
            i := i + 1 ;
        }
}