from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def solve(n : int) -> int:
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() >= 0)
    Ensures((Result()) == (popcount(n)))
    # post-conditions-end

    # impl-start
    m : int = n
    r : int = 0
    while (m) > (0):
        # invariants-start
        Invariant(((0) <= (m)) and ((m) <= (n)))
        Invariant(r >= 0)
        Invariant(((r) + (popcount(m))) == (popcount(n)))
        # invariants-end
        r = (r) + ((m % 2))
        m = (m // 2)
    return r
    # impl-end

@Pure
def popcount(n : int) -> int :
    # pure-pre-conditions-start
    Requires(n >= 0)
    # pure-pre-conditions-end

    # pure-start
    if n == 0:
        return 0
    else:
        return (n % 2) + popcount(n // 2)
    # pure-end

