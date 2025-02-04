from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *


@Pure
def starts__with(s : List[int], p : List[int], i : int) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(Acc(list_pred(p), 1/2))
    Requires(i >= 0 and i <= len(p) and i <= len(s))
    # pure-pre-conditions-end
    # pure-post-conditions-start
    Ensures(Implies(len(p) == i and len(s) >= len(p), Result()))
    Ensures(Implies(len(s) < len(p), not Result()))
    # pure-post-conditions-end

    # pure-start
    return len(s) >= len(p) and Forall(int, lambda x: Implies(x >= i and x < len(p), s[x] == p[x]))
    # pure-end

@Pure
def starts__with__fun(s : List[int], p : List[int], i : int) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(Acc(list_pred(p), 1/2))
    Requires(0 <= i and i <= len(p) and i <= len(s))
    # pure-pre-conditions-end
    # pure-post-conditions-start
    Ensures(Result() == starts__with(s, p, i))
    # pure-post-conditions-end

    # pure-start
    if (len(p) == i):
        return True
    if (len(s) > i and len(s) >= len(p) and s[i] == p[i]):
        return starts__with(s, p, i + 1)
    return False
    # pure-end

def filter__by__prefix(xs : List[List[int]], p : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(xs)))
    Requires(Acc(list_pred(p)))
    Requires(Forall(xs, lambda x : Acc(list_pred(x))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(p)))
    Ensures(Acc(list_pred(xs)))
    Ensures(Forall(xs, lambda x : Acc(list_pred(x))))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda j: 
        Implies(j >= 0 and j < len(Result()), Result()[j] >= 0 and Result()[j] < len(xs))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or (starts__with(xs[Result()[i]], p, 0))))
    # post-conditions-end

    # impl-start
    filtered : List[int] = []
    i : int = 0
    while (i) < (len(xs)):
        # invariants-start
        Invariant(Acc(list_pred(filtered)))
        Invariant(Acc(list_pred(xs), 1/2))
        Invariant(Acc(list_pred(p), 1/2))
        Invariant(((0) <= (i)) and ((i) <= (len(xs))))
        Invariant(Forall(xs, lambda x : Acc(list_pred(x))))
        Invariant(Forall(filtered, lambda j:
            (j >= 0 and j < i)))
        Invariant(Forall(filtered, lambda i:
            (starts__with(xs[i], p, 0), [[starts__with(xs[i], p, 0)]])))
        # invariants-end
        if starts__with__fun((xs)[i], p, 0):
            filtered = (filtered) + [i]
        i = (i) + (1)
    return filtered
    # impl-end
