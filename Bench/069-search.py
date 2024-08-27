from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def freq_req(i : int, j : int, s : List[int], x : int) -> int: 
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    if i == j:
        return 0
    else:
        return ((s)[j - 1] == x) + (freq_req(i, j - 1, s, x))

def freq(s : List[int], x : int) -> int:
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(s)))
    Ensures(Result() == freq_req(0, len(s), s, x))
    count = int(0) # type : int
    count = 0
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (len(s)):
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(s))))
        Invariant(Forall(int, lambda y : (Implies(y >= 0 and y < len(s), freq_req(0, y + 1, s, x) == freq_req(0, y, s, x) + (s[y] == x)), [[freq_req(0, y + 1, s, x)]])))
        Invariant(count == freq_req(0, d_1_i_, s, x))
        Assert(freq_req(0, d_1_i_ + 1, s, x) == freq_req(0, d_1_i_, s, x) + (s[d_1_i_] == x))
        if ((s)[d_1_i_]) == (x):
            count = (count) + (1)
        d_1_i_ = (d_1_i_) + (1)
    return count
