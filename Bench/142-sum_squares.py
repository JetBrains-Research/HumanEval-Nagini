from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def checkVal(x : int) -> int: 
    # pure-start
    if x % 3 == 0:
        return x * x
    elif x % 4 == 0 and x % 3 != 0:
        return x * x * x
    else:
        return x
    # pure-end

@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pure-pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return checkVal((s)[j - 1]) + (psum(i, j - 1, s))
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
        Invariant(Forall(int, lambda i: (not (((0) <= (i)) and ((i) < (len(lst)))) or 
            (psum(0, i + 1, lst) == checkVal(lst[i]) + psum(0, i, lst)), [[psum(0, i + 1, lst)]])))
        Invariant((r) == (psum(0, k, lst)))
        # invariants-end
        r = r + checkVal(lst[k])
        k = (k) + (1)
    return r
    # impl-end
