from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def smallest__change__fun(s : List[int], i : int, j : int) -> int:
    Requires(Acc(list_pred(s)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(s) // 2)))
    Ensures((Result()) >= (0))
    if i == j:
        return 0
    else:
        if (s)[j - 1] != (s)[len(s) - j]:
            return 1 + (smallest__change__fun(s, i, j - 1))
        else:
            return smallest__change__fun(s, i, j - 1)

def smallest__change(s : List[int]) -> int:
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == (smallest__change__fun(s, 0, len(s) // 2)))
    c = int(0) # type : int
    c = 0
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < ((len(s) // 2)):
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= ((len(s) // 2))))
        Invariant(Forall(int, lambda d_0_i_: (Implies(d_0_i_ >= 0 and d_0_i_ < len(s) // 2, smallest__change__fun(s, 0, d_0_i_ + 1) == (smallest__change__fun(s, 0, d_0_i_) + 1 if (s)[d_0_i_] != (s)[len(s) - d_0_i_ - 1] else smallest__change__fun(s, 0, d_0_i_))), [[smallest__change__fun(s, 0, d_0_i_ + 1)]])))
        Invariant(c == smallest__change__fun(s, 0, d_1_i_))
        Assert(smallest__change__fun(s, 0, d_1_i_ + 1) == (smallest__change__fun(s, 0, d_1_i_) + 1 if (s)[d_1_i_] != (s)[len(s) - d_1_i_ - 1] else smallest__change__fun(s, 0, d_1_i_)))
        if ((s)[d_1_i_]) != ((s)[((len(s)) - (1)) - (d_1_i_)]):
            c = (c) + (1)
        d_1_i_ = (d_1_i_) + (1)
    return c