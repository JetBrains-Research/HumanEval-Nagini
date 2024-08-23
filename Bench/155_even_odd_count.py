from typing import List, Tuple
from nagini_contracts.contracts import *

def even__odd__count(n : int) -> Tuple[int, int]:
    Requires((n) > (0))
    Ensures((Result()[0]) == (even__count(n)))
    Ensures((Result()[1]) == (odd__count(n)))
    even = int(0) # type : int
    odd = int(0) # type : int
    d_0_num_ = n # type : int
    while (d_0_num_) > (0):
        Invariant(((0) <= (d_0_num_)))
        Invariant(n > 0)
        Invariant(((even) + (even__count(d_0_num_))) == (even__count(n)))
        Invariant(((odd) + (odd__count(d_0_num_))) == (odd__count(n)))
        even = (even) + ((d_0_num_ % 2) == 0)
        odd = (odd) + (d_0_num_ % 2)
        d_0_num_ = (d_0_num_ // 10)
    return (even, odd)

@Pure
def odd__count(n : int) -> int :
    Requires(n >= 0)
    if n == 0:
        return 0
    else:
        return (n % 2) + odd__count(n // 10)

@Pure
def even__count(n : int) -> int :
    Requires(n >= 0)
    if n == 0:
        return 0
    else:
        return ((n % 2) == 0) + even__count(n // 10)
