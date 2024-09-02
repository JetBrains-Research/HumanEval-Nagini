from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def solve(n : int) -> int:
    Requires((n) >= (0))
    Ensures(Result() >= 0)
    Ensures((Result()) == (popcount(n)))
    r = int(0) # type : int
    d_0_m_ = int(0) # type : int
    d_0_m_ = n
    r = 0
    while (d_0_m_) > (0):
        Invariant(((0) <= (d_0_m_)) and ((d_0_m_) <= (n)))
        Invariant(r >= 0)
        Invariant(((r) + (popcount(d_0_m_))) == (popcount(n)))
        r = (r) + ((d_0_m_ % 2))
        d_0_m_ = (d_0_m_ // 2)
    return r

@Pure
def popcount(n : int) -> int :
    Requires(n >= 0)
    if n == 0:
        return 0
    else:
        return (n % 2) + popcount(n // 2)

