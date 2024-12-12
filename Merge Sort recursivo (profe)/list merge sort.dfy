include @"list datatype.dfy"
include @".\increasing lists.dfy"

function merge_sort (l : List<a>) : (l' : List<a>)
ensures increasing (l')
ensures permutation (l, l')
decreases len(l)
{
    match l
        case Nil => l
        case Cons (x, Nil) => l
        case Cons (x, Cons (y, xs)) => var (ls, rs) := split <a> (l) ;
                                        assert len (l) > 1 ; //assert len (ls) < len (l) ;
                                       var ls' := merge_sort (ls) ;
                                       var rs' := merge_sort (rs) ;
                                        assert permutation (l, appnd (ls, rs)) ;
                                        perm_appnd (ls, rs, ls', rs') ;
                                        assert permutation (appnd (ls, rs), appnd (ls', rs')) ;
                                       merge (ls', rs')
}