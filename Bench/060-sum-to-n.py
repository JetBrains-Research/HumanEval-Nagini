from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def psum(i : int, j : int) -> int :
    Requires(0 <= i and i <= j + 1)
    if i > j:
        return 0
    else:
        return j + 1 + (psum(i, j - 1))
    
def sum__squares(n : int) -> int:
    Requires((n) >= (1))
    Ensures((Result()) == (psum(0, n - 1)))
    r = int(0) # type : int
    r = 0
    d_2_k_ = int(0) # type : int
    d_2_k_ = 0
    while (d_2_k_) < (n):
        Invariant(((0) <= (d_2_k_)) and ((d_2_k_) <= (n)))
        Invariant((r) == (psum(0, d_2_k_ - 1)))
        r = (r) + ((d_2_k_) + (1))
        d_2_k_ = (d_2_k_) + (1)
    return r