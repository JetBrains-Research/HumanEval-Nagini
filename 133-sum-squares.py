from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    if i == j:
        return 0
    else:
        return (s)[j - 1] * (s)[j - 1] + (psum(i, j - 1, s))

def sum__squares(lst : List[int]) -> int:
    Requires(Acc(list_pred(lst)))
    Ensures(Acc(list_pred(lst)))
    Ensures((Result()) == (psum(0, len(lst), lst)))
    r = int(0) # type : int
    r = 0
    d_2_k_ = int(0) # type : int
    d_2_k_ = 0
    while (d_2_k_) < (len(lst)):
        Invariant(Acc(list_pred(lst)))
        Invariant(((0) <= (d_2_k_)) and ((d_2_k_) <= (len(lst))))
        Invariant((r) == (psum(0, d_2_k_, lst)))
        Invariant(Forall(int, lambda d_2_i_: (not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(lst)))) or ((psum(0, d_2_i_ + 1, lst)) == (psum(0, d_2_i_, lst) + lst[d_2_i_] * lst[d_2_i_])), [[psum(0, d_2_i_ + 1, lst)]])))
        r = (r) + ((lst)[d_2_k_]) * ((lst)[d_2_k_])
        d_2_k_ = (d_2_k_) + (1)
    return r
