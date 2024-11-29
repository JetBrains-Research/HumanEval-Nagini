from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def lower(c : int) -> bool :
    # pure-start
    return ((0) <= (c)) and ((c) <= (25))
    # pure-end

@Pure
def upper(c : int) -> bool :
    # pure-start
    return ((26) <= (c)) and ((c) <= (51))
    # pure-end

@Pure
def alpha(c : int) -> bool :
    # pure-start
    return (lower(c)) or (upper(c))
    # pure-end

def flip__char(c : int) -> int :
    # pre-conditions-start
    Ensures(lower(c) == upper(Result()))
    Ensures(upper(c) == lower(Result()))
    # pre-conditions-end

    # pure-start
    if lower(c):
        return ((c) - (0)) + (26)
    elif upper(c):
        return ((c) + (0)) - (26)
    elif True:
        return c
    # pure-end

def flip__case(s : List[int]) -> List[int] :
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (len(s)))
    Ensures(Forall(int, lambda d_0_i_: (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(s))), lower((s)[d_0_i_]) == upper((Result())[d_0_i_])))))
    Ensures(Forall(int, lambda d_0_i_: (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(s))), upper((s)[d_0_i_]) == lower((Result())[d_0_i_])))))
    # post-conditions-end

    # impl-start
    res : List[int] = list([int(0)] * len(s))
    i : int = int(0)
    while i < len(s):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(Acc(list_pred(res)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant((len(res)) == (len(s)))
        Invariant(Forall(int, lambda d_0_i_: (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (i)), lower((s)[d_0_i_]) == upper((res)[d_0_i_])))))
        Invariant(Forall(int, lambda d_0_i_: (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (i)), upper((s)[d_0_i_]) == lower((res)[d_0_i_])))))
        # invariants-end
        res[i] = flip__char(s[i])
        i = i + 1
    return res
    # impl-end
