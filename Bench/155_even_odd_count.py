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
    num : int = n
    while (num) > (0):
        # invariants-start
        Invariant(((0) <= (num)))
        Invariant(n > 0)
        Invariant(((even) + (even__count(num))) == (even__count(n)))
        Invariant(((odd) + (odd__count(num))) == (odd__count(n)))
        # invariants-end
        even = (even) + ((num % 2) == 0)
        odd = (odd) + (num % 2)
        num = (num // 10)
    return (even, odd)
    # impl-end

@Pure
def odd__count(n : int) -> int :
    # pure-pre-conditions-start
    Requires(n >= 0)
    # pure-pre-conditions-end

    # pure-start
    if n == 0:
        return 0
    else:
        return (n % 2) + odd__count(n // 10)
    # pure-end

@Pure
def even__count(n : int) -> int :
    # pure-pre-conditions-start
    Requires(n >= 0)
    # pure-pre-conditions-end

    # pure-start
    if n == 0:
        return 0
    else:
        return ((n % 2) == 0) + even__count(n // 10)
    # pure-end
