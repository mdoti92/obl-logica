datatype List<a> = Nil
                 | Cons (hd : a, tl : List<a>)

function ms <a> (l : List) : multiset
{
    match l 
        case Nil  => multiset{}
        case Cons (x, xs) => var s := ms (xs) ;
                             s [x := s[x] + 1]
}

lemma ms_Cons <a> (x: a, l : List)
 ensures ms (Cons (x, l)) == ms (l) + multiset{x}
{}

function len <a> (l : List) : nat
{
    match l
        case Nil => 0
        case Cons (_, xs) => 1 + len (xs)
}

function appnd <a> (l : List, l' : List) : (r : List)
ensures len (r) == len (l) + len (l')
{
    match l
        case Nil => l'
        case Cons (x, xs) => Cons (x, appnd (xs, l'))
}

predicate permutation <a> (l : List, l' : List)
{ms(l) == ms(l')}
/*
lemma perm_symm <a> (l : List, l' : List)
 requires permutation (l, l')
 ensures permutation (l', l)
{}

lemma perm_trans <a> (l : List, l' : List, l'' : List)
 requires permutation (l, l')
 requires permutation (l', l'')
 ensures permutation (l, l'')
{}
*/
lemma ms_appnd <a> (l : List, l' : List)
 ensures ms (appnd (l, l')) == ms (l) + ms (l')
{}
lemma ms_appnd' <a> (x: a, l : List, y: a, l' : List)
 ensures ms (appnd (Cons (x, l), Cons (y, l'))) == multiset{x, y} + ms (l) + ms (l')
{
     calc{
        ms (appnd (Cons (x, l), Cons (y, l'))) ;
     == {ms_appnd (Cons (x, l), Cons (y, l')) ;}
        ms (Cons (x, l)) + ms (Cons (y, l')) ; 
     == {ms_Cons (x, l) ; ms_Cons (y, l') ;}
        multiset{x, y} + ms (l) + ms (l') ;
     //   multiset{x} + ms (l) + multiset{y} + ms (l') ; 
    }
}

lemma perm_appnd <a> (l1 : List, l2 : List, l'1 : List, l'2 : List)
 requires permutation (l1, l'1)
 requires permutation (l2, l'2)
 ensures permutation (appnd (l1, l2), appnd (l'1, l'2))
{
  ms_appnd (l1, l2) ; ms_appnd (l'1, l'2) ;  
}

function split <a> (l : List) : (r : (List, List))
ensures var (ls, rs) := r ;
        permutation (l, appnd (ls, rs))
    &&  (len (l) > 1 ==> len (ls) < len (l) && len (rs) < len (l))
{
    match l
        case Nil => (Nil, Nil)
        case Cons (x, Nil) => (l, Nil)
        case Cons (x, Cons (y, xs)) => var (ls, rs) := split (xs) ;
                                       assert len (l) == 2 + len (xs) ;
                                       ms_appnd (ls, rs) ;
                                       ms_appnd' (x, ls, y, rs) ;
                                       (Cons (x, ls), Cons (y, rs))
}

