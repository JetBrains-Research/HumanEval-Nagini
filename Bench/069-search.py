from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def freq_req(i : int, j : int, s : List[int], x : int) -> int: 
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pure-pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return ((s)[j - 1] == x) + (freq_req(i, j - 1, s, x))
    # pure-end

def freq(s : List[int], x : int) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Result() == freq_req(0, len(s), s, x))
    # post-conditions-end

    # impl-start
    count : int = 0
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant(Forall(int, lambda y : (Implies(y >= 0 and y < len(s), freq_req(0, y + 1, s, x) == freq_req(0, y, s, x) + (s[y] == x)), [[freq_req(0, y + 1, s, x)]])))
        Invariant(count == freq_req(0, i, s, x))
        # invariants-end
        # assert-start
        Assert(freq_req(0, i + 1, s, x) == freq_req(0, i, s, x) + (s[i] == x))
        # assert-end
        if ((s)[i]) == (x):
            count = (count) + (1)
        i = (i) + (1)
    return count
    # impl-end

