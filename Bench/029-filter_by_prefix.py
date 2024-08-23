from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *


@Pure
def starts__with(s : List[int], p : List[int], i : int) -> bool :
    Requires(Acc(list_pred(s), 1/2))
    Requires(Acc(list_pred(p), 1/2))
    Requires(i >= 0 and i <= len(p) and i <= len(s))
    Ensures(Implies(len(p) == i and len(s) >= len(p), Result()))
    Ensures(Implies(len(s) < len(p), not Result()))
    return len(s) >= len(p) and Forall(int, lambda x: Implies(x >= i and x < len(p), s[x] == p[x]))

@Pure
def starts__with__fun(s : List[int], p : List[int], i : int) -> bool :
    Requires(Acc(list_pred(s), 1/2))
    Requires(Acc(list_pred(p), 1/2))
    Requires(0 <= i and i <= len(p) and i <= len(s))
    Ensures(Result() == starts__with(s, p, i))
    if (len(p) == i):
        return True
    if (len(s) > i and len(s) >= len(p) and s[i] == p[i]):
        return starts__with(s, p, i + 1)
    return False

def filter__by__prefix(xs : List[List[int]], p : List[int]) -> List[int]:
    Requires(Acc(list_pred(xs)))
    Requires(Acc(list_pred(p)))
    Requires(Forall(xs, lambda x : Acc(list_pred(x))))
    Ensures(Acc(list_pred(p)))
    Ensures(Acc(list_pred(xs)))
    Ensures(Forall(xs, lambda x : Acc(list_pred(x))))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_2_j_: 
        Implies(d_2_j_ >= 0 and d_2_j_ < len(Result()), Result()[d_2_j_] >= 0 and Result()[d_2_j_] < len(xs))))
    Ensures(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(Result())))) or (starts__with(xs[Result()[d_0_i_]], p, 0))))
    filtered = list([int(0)] * 0) # type : List[int]
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (len(xs)):
        Invariant(Acc(list_pred(filtered)))
        Invariant(Acc(list_pred(xs), 1/2))
        Invariant(Acc(list_pred(p), 1/2))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(xs))))
        Invariant(Forall(xs, lambda x : Acc(list_pred(x))))
        Invariant(Forall(filtered, lambda i:
            (i >= 0 and i < d_1_i_)))
        Invariant(Forall(filtered, lambda i:
            (starts__with(xs[i], p, 0), [[starts__with(xs[i], p, 0)]])))
        if starts__with__fun((xs)[d_1_i_], p, 0):
            filtered = (filtered) + [d_1_i_]
        d_1_i_ = (d_1_i_) + (1)
    return filtered