from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def psum(i : int, j : int) -> int :
    # pre-conditions-start
    Requires(0 <= i and i <= j + 1)
    # pre-conditions-end

    # pure-start
    if i > j:
        return 0
    else:
        return j + 1 + (psum(i, j - 1))
    # pure-end
    
def sum__squares(n : int) -> int:
    # pre-conditions-start
    Requires((n) >= (1))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) == (psum(0, n - 1)))
    # post-conditions-end

    # impl-start
    r : int = 0
    k : int = 0
    while (k) < (n):
        # invariants-start
        Invariant(((0) <= (k)) and ((k) <= (n)))
        Invariant((r) == (psum(0, k - 1)))
        # invariants-end
        r = (r) + ((k) + (1))
        k = (k) + (1)
    return r
    # impl-end
