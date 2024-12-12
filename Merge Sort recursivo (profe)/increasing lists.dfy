include @".\list datatype.dfy"

type a {predicate leq (x : a)}

predicate minor (x : a, l : List <a>)
{l.Nil? || (x.leq (l.hd) && minor (x, l.tl))}

predicate increasing (l : List<a>)
{l.Nil? || (minor (l.hd, l.tl) && increasing (l.tl))}

function merge (l : List<a>, l' : List<a>) : (r : List<a>)
 requires increasing (l) && increasing (l')
 ensures increasing (r)
 ensures permutation (r, appnd (l, l'))
{
    match l
        case Nil => l'
        case Cons (x, xs) => match l' {
                                case Nil => l
                                case Cons (y, ys) => if x.leq (y)
                                                     then Cons (x, merge (xs, l'))
                                                     else Cons (y, merge (l, ys))
        }
}