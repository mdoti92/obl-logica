method maximo (a : nat, b : nat) returns (m: nat)
ensures m >= a && m >= b
ensures m == a || m == b
{
    m := if a > b then a else b;
}