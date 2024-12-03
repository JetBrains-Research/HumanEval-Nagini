from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def Sum(a : List[int], s : int, t : int) -> int :
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    Requires(((0) <= (s)) and ((s) <= (t)) and ((t) <= (len(a))))
    # pre-conditions-end

    # pure-start
    if s == t:
        return 0
    else:
        return (a)[t - 1] + (Sum(a, s, t - 1))
    # pure-end

def minSubArraySum(a : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a)))
    Ensures(Forall(int, lambda p:
        Forall(int, lambda q:
            not ((((0) <= (p)) and ((p) <= (q))) and ((q) <= (len(a)))) or ((Sum(a, p, q)) >= (Result())))))
    Ensures(Exists(int, lambda k:
        Exists(int, lambda m:
            ((((0) <= (k)) and ((k) <= (m))) and ((m) <= (len(a)))) and ((Result()) == (Sum(a, k, m))))))
    # post-conditions-end

    # impl-start
    s : int = int(0)
    k : int = int(0)
    m : int = int(0)
    n : int = int(0)
    c : int = int(0)
    t : int = int(0)
    while (n) < (len(a)):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(((0) <= (n)) and ((n) <= (len(a))))
        Invariant(Forall(int, lambda p: (Implies(0 <= p and p < len(a), Sum(a, 0, p + 1) == Sum(a, 0, p) + a[p]))))
        Invariant(Forall(int, lambda st: 
            Implies(st >= 0 and st < len(a), 
                Forall(int, lambda p: (Implies(st <= p and p < len(a), Sum(a, st, p + 1) == Sum(a, st, p) + a[p]))))))
        Invariant(((((0) <= (c)) and ((c) <= (n))) and ((n) <= (len(a)))))
        Invariant(((t) == (Sum(a, c, n))))
        Invariant(((((0) <= (k)) and ((k) <= (m))) and ((m) <= (n))))
        Invariant(((s) == (Sum(a, k, m))))
        Invariant(Forall(int, lambda b:
            not (((0) <= (b)) and ((b) <= (n))) or ((Sum(a, b, n)) >= (Sum(a, c, n)))))
        Invariant(Sum(a, c, n) >= Sum(a, k, m))
        Invariant(Forall(int, lambda p:
            Forall(int, lambda q:
                (not ((((0) <= (p)) and ((p) <= (q))) and ((q) <= (n))) or ((Sum(a, p, q)) >= (Sum(a, k, m))), [[Sum(a, p, q)]]))))
        # invariants-end

        # assert-start
        Assert(Sum(a, c, n + 1) == Sum(a, c, n) + a[n]) 
        # assert-end
        t = (t) + ((a)[n])
        n = (n) + (1)
        if (t) > (0):
            c = n
            t = 0
        elif (s) > (t):
            k = c
            m = n
            s = t
    return s
    # impl-end

