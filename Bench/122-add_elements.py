from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def sum__chars__rec(i : int, j : int, lst : List[int]) -> int :
    Requires(Acc(list_pred(lst)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(lst))))
    if i == j:
        return 0
    else:
        return ((lst)[j - 1] if (lst)[j - 1] < 100 else 0) + sum__chars__rec(i, j - 1, lst)

def SumElementsWithAtMostTwoDigits(lst : List[int], k : int) -> int:
    Requires(Acc(list_pred(lst)))
    Requires(1 <= k and k <= len(lst))
    Ensures(Acc(list_pred(lst)))
    Ensures(1 <= k and k <= len(lst))
    Ensures(Result() == sum__chars__rec(0, k, lst))
    sum = int(0) # type : int
    sum = 0
    d_3_i_ = int(0) # type : int
    d_3_i_ = 0
    while d_3_i_ < k:
        Invariant(Acc(list_pred(lst)))
        Invariant(1 <= k and k <= len(lst))
        Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= (len(lst))) and d_3_i_ <= k)
        Invariant(Forall(int, lambda d_3_i_ : (Implies(d_3_i_ >= 0 and d_3_i_ < k, sum__chars__rec(0, d_3_i_ + 1, lst) == sum__chars__rec(0, d_3_i_, lst) + ((lst)[d_3_i_] if (lst)[d_3_i_] < 100 else 0)), [[sum__chars__rec(0, d_3_i_ + 1, lst)]])))
        Invariant((sum) == (sum__chars__rec(0, d_3_i_, lst)))
        Assert(sum__chars__rec(0, d_3_i_ + 1, lst) == sum__chars__rec(0, d_3_i_, lst) + ((lst)[d_3_i_] if (lst)[d_3_i_] < 100 else 0))
        if (lst)[d_3_i_] < 100:
            sum = (sum) + ((lst)[d_3_i_])
        d_3_i_ = (d_3_i_) + (1)
    return sum