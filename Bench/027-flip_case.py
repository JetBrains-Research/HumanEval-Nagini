from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def lower(c : int) -> bool :
    return ((0) <= (c)) and ((c) <= (25))

@Pure
def upper(c : int) -> bool :
    return ((26) <= (c)) and ((c) <= (51))

@Pure
def alpha(c : int) -> bool :
    return (lower(c)) or (upper(c))

@Pure
def flip__char(c : int) -> int :
    Ensures(lower(c) == upper(Result()))
    Ensures(upper(c) == lower(Result()))
    if lower(c):
        return ((c) - (0)) + (26)
    elif upper(c):
        return ((c) + (0)) - (26)
    elif True:
        return c

def flip__case(s : List[int]) -> List[int] :
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (len(s)))
    Ensures(Forall(int, lambda d_0_i_: (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(s))), lower((s)[d_0_i_]) == upper((Result())[d_0_i_])))))
    Ensures(Forall(int, lambda d_0_i_: (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(s))), upper((s)[d_0_i_]) == lower((Result())[d_0_i_])))))
    res = list([int(0)] * len(s)) # type : List[int]
    i = int(0) # type : int
    while i < len(s):
        Invariant(Acc(list_pred(s)))
        Invariant(Acc(list_pred(res)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant((len(res)) == (len(s)))
        Invariant(Forall(int, lambda d_0_i_: (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (i)), lower((s)[d_0_i_]) == upper((res)[d_0_i_])))))
        Invariant(Forall(int, lambda d_0_i_: (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (i)), upper((s)[d_0_i_]) == lower((res)[d_0_i_])))))
        res[i] = flip__char(s[i])
        i = i + 1
    return res
