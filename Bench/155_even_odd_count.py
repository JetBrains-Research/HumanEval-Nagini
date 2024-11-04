from typing import List, Tuple
from nagini_contracts.contracts import *

def even__odd__count(n : int) -> Tuple[int, int]:
    # pre-conditions-start
    Requires((n) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()[0]) == (even__count(n)))
    Ensures((Result()[1]) == (odd__count(n)))
    # post-conditions-end

    # impl-start
    even : int = int(0)
    odd : int = int(0)
    d_0_num_ : int = n
    while (d_0_num_) > (0):
        # invariants-start
        Invariant(((0) <= (d_0_num_)))
        Invariant(n > 0)
        Invariant(((even) + (even__count(d_0_num_))) == (even__count(n)))
        Invariant(((odd) + (odd__count(d_0_num_))) == (odd__count(n)))
        # invariants-end
        even = (even) + ((d_0_num_ % 2) == 0)
        odd = (odd) + (d_0_num_ % 2)
        d_0_num_ = (d_0_num_ // 10)
    return (even, odd)
    # impl-end

@Pure
def odd__count(n : int) -> int :
    # pre-conditions-start
    Requires(n >= 0)
    # pre-conditions-end

    # impl-start
    if n == 0:
        return 0
    else:
        return (n % 2) + odd__count(n // 10)
    # impl-end

@Pure
def even__count(n : int) -> int :
    # pre-conditions-start
    Requires(n >= 0)
    # pre-conditions-end

    # impl-start
    if n == 0:
        return 0
    else:
        return ((n % 2) == 0) + even__count(n // 10)
    # impl-end
