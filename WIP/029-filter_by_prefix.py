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

# @Pure
# def starts__with__fun(s : List[int], p : List[int], i : int) -> bool :
#     Requires(Acc(list_pred(s), 1/2))
#     Requires(Acc(list_pred(p), 1/2))
#     Requires(0 <= i and i <= len(p) and i <= len(s))
#     # Ensures(Implies(len(p) == i, len(s) >= len(p) and Forall(int, lambda x: x >= i and x < len(p) and s[x] == p[x]) and Result()))
#     # Ensures(Implies(len(p) == i, Result() == starts__with(s,p, i)))
#     # Ensures(Result() == starts__with(s, p, i))
#     if (len(p) == i):
#         return True
#     if (len(s) > i and len(s) >= len(p) and s[i] == p[i]):
#         return starts__with(s, p, i + 1)
#     return False

def filter__by__prefix(xs : List[List[int]], p : List[int]) -> List[int]:
    Requires(Acc(list_pred(xs)))
    Requires(Acc(list_pred(p)))
    Requires(Forall(xs, lambda x : Acc(list_pred(x))))
    # Requires(Forall(int, lambda x : (Implies(x >= 0 and x < len(xs), Acc(list_pred(xs[x]))))))
    Ensures(Acc(list_pred(p)))
    Ensures(Acc(list_pred(xs)))
    # Ensures(Forall(int, lambda x : (Implies(x >= 0 and x < len(xs), Acc(list_pred(xs[x]))))))
    Ensures(Acc(list_pred(Result())))
    # Ensures(Forall(int, lambda x : Implies(x >= 0 and x < len(Result()), Acc(list_pred(Result()[x])))))
    # Ensures(Forall(int, lambda d_0_i_:
    #     not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(Result())))) or (starts__with(Result()[d_0_i_], p, 0))))
    filtered = list([int(0)] * 0) # type : List[int]
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (len(xs)):
        Invariant(Acc(list_pred(filtered)))
        Invariant(Acc(list_pred(xs), 1/2))
        Invariant(Acc(list_pred(p), 1/2))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(xs))))
        Invariant(Forall(xs, lambda x : Acc(list_pred(x))))
        Invariant(Forall(int, lambda d_2_j_: Implies(d_2_j_ >= 0 and d_2_j_ < len(filtered), filtered[d_2_j_] >= 0 and filtered[d_2_j_] < d_1_i_)))
        # Invariant(Forall(filtered, lambda x : Acc(list_pred(x))))
        # Invariant(Forall(int, lambda x : (Implies(x >= 0 and x < len(filtered), Acc(list_pred(filtered[x]))), [[filtered[x]]])))
        # Invariant(Forall(int, lambda x : (Implies(x >= 0 and x < len(xs), Acc(list_pred(xs[x]))))))
        # Invariant(Forall(filtered, lambda x:
        #     (starts__with(x, p, 0), [[starts__with(x, p, 0)]])))
        # Invariant(Forall(int, lambda d_2_j_:
        #     (Implies(((0) <= (d_2_j_)) and ((d_2_j_) < (len(filtered))), starts__with(xs[(filtered)[d_2_j_]], p, 0)), [[starts__with(xs[(filtered)[d_2_j_]], p, 0)]])))
        # Invariant(Forall(int, lambda d_2_j_:
        #     (Implies(((0) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_)) and starts__with(xs[d_2_j_], p, 0), 
        #             Exists(int, lambda x: x >= 0 and x < len(filtered) and filtered[x] == d_2_j_)), 
        #     [[xs[d_2_j_]]])))
        Assume(Forall(int, lambda d_2_j_:
            (Implies(((0) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_)) and starts__with(xs[d_2_j_], p, 0), 
                    Exists(int, lambda x: x >= 0 and x < len(filtered) and filtered[x] == d_2_j_)), 
            [[xs[d_2_j_]]])))
        if starts__with((xs)[d_1_i_], p, 0):
            filtered = (filtered) + [d_1_i_]
            Assert(starts__with(xs[(filtered)[len(filtered) - 1]], p, 0))
            Assert(d_1_i_ == filtered[len(filtered) - 1])
            Assert(Exists(int, lambda x: x >= 0 and x < len(filtered) and filtered[x] == d_1_i_))
        Assert(Forall(int, lambda d_2_j_:
            (Implies(((0) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_)) and starts__with(xs[d_2_j_], p, 0), 
                    Exists(int, lambda x: x >= 0 and x < len(filtered) and filtered[x] == d_2_j_)), 
            [[xs[d_2_j_]]])))
        Assert(Forall(int, lambda d_2_j_:
            (Implies(((0) <= (d_2_j_)) and ((d_2_j_) <= (d_1_i_)) and starts__with(xs[d_2_j_], p, 0), 
                    Exists(int, lambda x: x >= 0 and x < len(filtered) and filtered[x] == d_2_j_)), 
            [[xs[d_2_j_]]])))
        d_1_i_ = (d_1_i_) + (1)
        Assert(Forall(int, lambda d_2_j_:
            (Implies(((0) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_)) and starts__with(xs[d_2_j_], p, 0), 
                    Exists(int, lambda x: x >= 0 and x < len(filtered) and filtered[x] == d_2_j_)), 
            [[xs[d_2_j_]]])))
        # Assert(Implies(((0) <= (d_1_i_)) and ((d_1_i_) < (d_1_i_)) and starts__with(xs[d_1_i_], p, 0), 
        #     Exists(int, lambda x: x >= 0 and x < len(filtered) and filtered[x] == d_1_i_)))
    return filtered