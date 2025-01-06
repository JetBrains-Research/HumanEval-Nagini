from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j + 1 and j < len(s))
    # pure-pre-conditions-end

    # pure-start
    if i > j:
        return 0
    else:
        return ((s)[j] if ((((j) % 2) == 0) and ((s)[j] % 2 == 1)) else 0) + (psum(i, j - 1, s))
    # pure-end

def add(v : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(v)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(v)))
    Ensures((Result()) == (psum(0, len(v) - 1, v)))
    # post-conditions-end

    # impl-start
    r : int = 0
    k : int = 0
    while (k) < (len(v)):
        # invariants-start
        Invariant(Acc(list_pred(v)))
        Invariant(((0) <= (k)) and ((k) <= (len(v))))
        Invariant((r) == (psum(0, k - 1, v)))
        # invariants-end
        r = (r) + (((v)[k] if ((((k) % 2) == 0) and ((v)[k] % 2 == 1)) else 0))
        k = (k) + (1)
    return r
    # impl-end
