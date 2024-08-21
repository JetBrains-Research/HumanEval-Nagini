from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def checkVal(x : int) -> int: 
    if x > 0 and x % 2 != 0:
        return x * x
    else:
        return 0
    
@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    if i == j:
        return 0
    else:
        return checkVal((s)[j - 1]) + (psum(i, j - 1, s))


def double__the__difference(lst : List[int]) -> int:
    Requires(Acc(list_pred(lst)))
    Ensures(Acc(list_pred(lst)))
    Ensures((Result()) == (psum(0, len(lst), lst)))
    r = int(0) # type : int
    r = 0
    d_3_k_ = int(0) # type : int
    d_3_k_ = 0
    while (d_3_k_) < (len(lst)):
        Invariant(Acc(list_pred(lst)))
        Invariant(((0) <= (d_3_k_)) and ((d_3_k_) <= (len(lst))))
        Invariant((r) == (psum(0, d_3_k_, lst)))
        Invariant(Forall(int, lambda d_3_i_: (not (((0) <= (d_3_i_)) and ((d_3_i_) < (len(lst)))) or 
            (psum(0, d_3_i_ + 1, lst) == checkVal(lst[d_3_i_]) + psum(0, d_3_i_, lst)), [[psum(0, d_3_i_ + 1, lst)]])))
        r = (r) + checkVal(((lst)[d_3_k_]))
        d_3_k_ = (d_3_k_) + (1)
    return r