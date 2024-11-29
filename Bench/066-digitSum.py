from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def upper__sum__rec(i : int, j : int, s : List[int]) -> int :
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(s))))
    # pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return s[j - 1] + upper__sum__rec(i, j - 1, s)
    # pure-end
    
def upper__sum(s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == (upper__sum__rec(0, len(s), s)))
    # post-conditions-end

    # impl-start
    res : int = 0
    d_1_i_ : int = 0
    while (d_1_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(s))))
        Invariant(Forall(int, lambda d_0_i_: (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(s))), upper__sum__rec(0, d_0_i_ + 1, s) == upper__sum__rec(0, d_0_i_, s) + s[d_0_i_]), [[upper__sum__rec(0, d_1_i_ + 1, s)]])))
        Invariant((res) == (upper__sum__rec(0, d_1_i_, s)))
        # invariants-end
        # assert-start
        Assert(upper__sum__rec(0, d_1_i_ + 1, s) == upper__sum__rec(0, d_1_i_, s) + s[d_1_i_])
        # assert-end
        res = (res) + (((s)[d_1_i_]))
        d_1_i_ = (d_1_i_) + (1)
    return res
    # impl-end

