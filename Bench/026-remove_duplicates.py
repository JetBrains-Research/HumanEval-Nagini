from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def remove__duplicates(a : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(len(a) == len(Old(a)))
    Ensures(len(a) >= len(Result()))
    Ensures(Forall(int, lambda i:
        Implies(((0) <= (i)) and ((i) < (len(a))) and (count__rec(a, a[i], len(a)) == 1), exists_check(Result(), a[i]))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or (count_check(a, (Result())[i]))))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    i : int = 0
    a_old = list(a)

    while (i) < (len(a)):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(a), 1/2))
        Invariant(Acc(list_pred(a_old), 1/2))
        Invariant(len(a) == len(a_old))
        Invariant(Forall(int, lambda i: (Implies(i >= 0 and i < len(a), a_old[i] == a[i]))))
        Invariant(((0) <= (i)) and ((i) <= (len(a))))
        Invariant(len(result) <= i)
        Invariant(Forall(int, lambda i:
            (Implies(((0) <= (i)) and ((i) < (i)) and (count__rec(a, a[i], len(a)) == 1), exists_check(result, a[i])), 
                [[]])))
        Invariant(Forall(int, lambda i:
            (not (((0) <= (i)) and ((i) < (len(result)))) or (count_check(a, (result)[i])), 
                [[]])))
        # invariants-end
        cnt : int = count__rec(a, (a)[i], len(a))
        if (cnt) == (1):
            result = (result) + [(a)[i]]
            # assert-start
            Assert(count__rec(a, result[len(result) - 1], len(a)) == 1)
            # assert-end
        i = (i) + (1)
    return result
    # impl-end

@Pure 
def exists_check(a : List[int], x : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    # pre-conditions-end

    # pure-start
    return Exists(int, lambda i:
        ((((0) <= (i)) and ((i) < (len((a)))) and ((a)[i]) == (x))))
    # pure-end

@Pure 
def count_check(a : List[int], x : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    # pre-conditions-end

    # pure-start
    return (count__rec(a, x, len(a))) == (1)
    # pure-end

@Pure
def count__rec(a : List[int], x : int, i : int) -> int :
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    Requires(((0) <= (i)) and ((i) <= (len(a))))
    # pre-conditions-end

    # pure-start
    if (i) == 0:
        return 0
    else:
        return (((a)[i - 1]) == (x)) + (count__rec(a, x, (i) - (1)))
    # pure-end
