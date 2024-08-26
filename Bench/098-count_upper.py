from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def count__upper__fun(s : List[int], i : int, j : int) -> int:
    Requires(Acc(list_pred(s)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(s))))
    Ensures((Result()) >= (0))
    if i == j:
        return 0
    else:
        if is__upper__vowel((s)[j - 1]) and (j - 1) % 2 == 0:
            return (1) + (count__upper__fun(s, i, j - 1))
        else:
            return count__upper__fun(s, i, j - 1)


def count__upper(s : List[int]) -> int:
    Requires(Acc(list_pred(s)))
    Ensures((Result()) >= (0))
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == (count__upper__fun(s, 0, len(s))))
    cnt = int(0) # type : int
    cnt = 0
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    
    while (d_1_i_) < (len(s)):
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(s))))
        Invariant(Forall(int, lambda d_0_i_: (Implies(d_0_i_ >= 0 and d_0_i_ < len(s), 
            count__upper__fun(s, 0, d_0_i_ + 1) == (count__upper__fun(s, 0, d_0_i_) + (1) if is__upper__vowel(s[d_0_i_]) and d_0_i_ % 2 == 0 else count__upper__fun(s, 0, d_0_i_))), 
                [[count__upper__fun(s, 0, d_0_i_ + 1)]])))
        Invariant((cnt) == (count__upper__fun(s, 0, d_1_i_)))
        Assert(count__upper__fun(s, 0, d_1_i_ + 1) == (count__upper__fun(s, 0, d_1_i_) + (1) if is__upper__vowel(s[d_1_i_]) and d_1_i_ % 2 == 0 else count__upper__fun(s, 0, d_1_i_)))
        if (is__upper__vowel((s)[d_1_i_])) and (((d_1_i_ % 2)) == (0)):
            cnt = (cnt) + (1)
        d_1_i_ = (d_1_i_) + (1)
    return cnt

@Pure
def is__upper__vowel(c : int) -> bool :
    return (((((c) == (0)) or ((c) == (1))) or ((c) == (2))) or ((c) == (3))) or ((c) == (4))
