from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def freq_req(i : int, j : int, s : List[int], x : int) -> int: 
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

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
    d_1_i_ : int = 0
    while (d_1_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(s))))
        Invariant(Forall(int, lambda y : (Implies(y >= 0 and y < len(s), freq_req(0, y + 1, s, x) == freq_req(0, y, s, x) + (s[y] == x)), [[freq_req(0, y + 1, s, x)]])))
        Invariant(count == freq_req(0, d_1_i_, s, x))
        # invariants-end
        # assert-start
        Assert(freq_req(0, d_1_i_ + 1, s, x) == freq_req(0, d_1_i_, s, x) + (s[d_1_i_] == x))
        # assert-end
        if ((s)[d_1_i_]) == (x):
            count = (count) + (1)
        d_1_i_ = (d_1_i_) + (1)
    return count
    # impl-end

