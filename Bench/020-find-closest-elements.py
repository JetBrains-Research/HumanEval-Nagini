from typing import List, Tuple
from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def dist(a : int, b : int) -> int :
    # pure-pre-conditions-start
    Ensures(Result() >= 0)
    # pure-pre-conditions-end

    # pure-start
    if (a) < (b):
        return (b) - (a)
    else:
        return (a) - (b)
    # pure-end

def find__closest__elements(s : List[int]) -> Tuple[int, int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires((len(s)) >= (2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(len(s) >= 2)
    Ensures(Exists(int, lambda a:
        Exists(int, lambda b:
            ((0 <= a and a < b and b < len(s)) and ((Result()[0]) == ((s)[a])) and (Result()[1]) == ((s)[b])))))
    Ensures(Forall(int, lambda a:
        Forall(int, lambda b:
            Implies((0 <= a and (a) < (len(s)) and 0 <= b and b < len(s)) and (a != b), (dist(Result()[0], Result()[1])) <= (dist((s)[a], (s)[b]))))))
    # post-conditions-end

    # impl-start
    l : int = (s)[0]
    h : int = (s)[1]
    d : int = dist(l, h)
    i : int = 0
    # assert-start
    Assert(Exists(int, lambda a:
        Exists(int, lambda b:
            ((0 <= a and (a) < (b) and b < len(s))) and ((l) == ((s)[a])) and ((h) == ((s)[b])))))
    # assert-end
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant((d) == (dist(l, h)))
        Invariant((len(s)) >= (2))
        Invariant(Exists(int, lambda a:
            Exists(int, lambda b:
                ((0 <= a and a < b and b < len(s) and ((l) == ((s)[a]))) and ((h) == ((s)[b]))))))
        Invariant(Forall(int, lambda x: 
            Forall(int, lambda y:
                (Implies((0 <= x and x < len(s) and 0 <= y and y < len(s)), dist(s[x], s[y]) == dist(s[y], s[x])), [[dist(s[x], s[y]) == dist(s[y], s[x])]]))))
        Invariant(Forall(int, lambda a:
            Forall(int, lambda b:
                (Implies((0 <= a and (a) < (i) and 0 <= b and b < len(s)) and (a != b), (dist(l, h)) <= (dist((s)[a], (s)[b]))), [[dist((s)[a], (s)[b])]]))))
        # invariants-end
        j : int = (i) + (1)
        # assert-start
        Assert(Forall(int, lambda a:
            Forall(int, lambda b:
                (Implies((0 <= a and (a) < (i) and 0 <= b and b < len(s)) and (a != b), (dist(l, h)) <= (dist((s)[a], (s)[b]))), [[dist((s)[a], (s)[b])]]))))
        Assert(Forall(int, lambda x: (Implies(x >= 0 and x < i, dist(l, h) <= dist(s[x], s[i])), [[dist(s[x], s[i])]])))
        # assert-end
        while (j) < (len(s)):
            # invariants-start
            Invariant(Acc(list_pred(s)))
            Invariant(((0) <= (i)) and ((i) < (len(s))))
            Invariant(((i) < (j)) and ((j) <= (len(s))))
            Invariant((d) == (dist(l, h)))
            Invariant((len(s)) >= (2))
            Invariant(Exists(int, lambda a:
                Exists(int, lambda b:
                    ((((0 <= a and a < b and b < len(s)) ) and ((l) == ((s)[a]))) and ((h) == ((s)[b]))))))
            Invariant(Forall(int, lambda x: 
                Forall(int, lambda y:
                    (Implies((0 <= x and x < len(s) and 0 <= y and y < len(s)), dist(s[x], s[y]) == dist(s[y], s[x])), [[dist(s[x], s[y]) == dist(s[y], s[x])]]))))
            Invariant(Forall(int, lambda x: (Implies(x >= 0 and x < i, dist(s[i], s[x]) == dist(s[x], s[i])), [[dist(s[i], s[x])]])))
            Invariant(Forall(int, lambda x: (Implies(x >= 0 and x < i, Implies(dist(l, h) <= dist(s[x], s[i]), dist(l, h) <= dist(s[i], s[x]))), [[dist(s[i], s[x])]])))
            Invariant(Forall(int, lambda x: (Implies(x >= 0 and x < i, dist(l, h) <= dist(s[x], s[i])), [[dist(s[x], s[i])]])))
            Invariant(Forall(int, lambda x: (Implies(x >= 0 and x < i, dist(l, h) <= dist(s[i], s[x])), [[dist(s[i], s[x])]])))
            Invariant(Forall(int, lambda a:
                Forall(int, lambda b:
                    (Implies((((a == (i) and i < b and b < j))) and (a != b), (dist(l, h)) <= (dist((s)[a], (s)[b]))), [[dist((s)[a], (s)[b])]]))))
            Invariant(Forall(int, lambda a:
                Forall(int, lambda b:
                    (Implies((((a == (i) and 0 <= b and b < j))) and (a != b), (dist(l, h)) <= (dist((s)[a], (s)[b]))), [[dist((s)[a], (s)[b])]]))))
            Invariant(Forall(int, lambda a:
                Forall(int, lambda b:
                    (Implies(((0 <= a and (a) < (i) and 0 <= b and b < len(s))) and (a != b), (dist(l, h)) <= (dist((s)[a], (s)[b]))), [[dist((s)[a], (s)[b])]]))))
            # invariants-end
            if i != j and (dist((s)[i], (s)[j])) <= (d):
                l = (s)[i]
                h = (s)[j]
                d = dist(l, h)
            j = (j) + (1)
        # assert-start
        Assert(Forall(int, lambda a:
            Forall(int, lambda b:
                (Implies((0 <= a and (a) <= (i) and 0 <= b and b < len(s)) and (a != b), (dist(l, h)) <= (dist((s)[a], (s)[b]))), [[dist((s)[a], (s)[b])]]))))
        # assert-end
        i = (i) + (1)
    return (l, h)
    # impl-end
