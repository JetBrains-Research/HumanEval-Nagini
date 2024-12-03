from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return (s)[j - 1] * (s)[j - 1] + (psum(i, j - 1, s))
    # pure-end

def sum__squares(lst : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(lst)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(lst)))
    Ensures((Result()) == (psum(0, len(lst), lst)))
    # post-conditions-end

    # impl-start
    r : int = 0
    k : int = 0
    while (k) < (len(lst)):
        # invariants-start
        Invariant(Acc(list_pred(lst)))
        Invariant(((0) <= (k)) and ((k) <= (len(lst))))
        Invariant((r) == (psum(0, k, lst)))
        Invariant(Forall(int, lambda i: (not (((0) <= (i)) and ((i) < (len(lst)))) or ((psum(0, i + 1, lst)) == (psum(0, i, lst) + lst[i] * lst[i])), [[psum(0, i + 1, lst)]])))
        # invariants-end
        r = (r) + ((lst)[k]) * ((lst)[k])
        k = (k) + (1)
    return r
    # impl-end
