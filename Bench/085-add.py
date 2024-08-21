from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j + 1 and j < len(s))
    if i > j:
        return 0
    else:
        return ((s)[j] if ((((j) % 2) == 1) and ((s)[j] % 2 == 0)) else 0) + (psum(i, j - 1, s))

def add(v : List[int]) -> int:
    Requires(Acc(list_pred(v)))
    Ensures(Acc(list_pred(v)))
    Ensures((Result()) == (psum(0, len(v) - 1, v)))
    r = int(0) # type : int
    r = 0
    d_2_k_ = int(0) # type : int
    d_2_k_ = 0
    while (d_2_k_) < (len(v)):
        Invariant(Acc(list_pred(v)))
        Invariant(((0) <= (d_2_k_)) and ((d_2_k_) <= (len(v))))
        Invariant((r) == (psum(0, d_2_k_ - 1, v)))
        r = (r) + (((v)[d_2_k_] if ((((d_2_k_) % 2) == 1) and ((v)[d_2_k_] % 2 == 0)) else 0))
        d_2_k_ = (d_2_k_) + (1)
    return r
