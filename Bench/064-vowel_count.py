from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def vowel__count(s : List[int]) -> int:
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) >= (0))
    Ensures(Result() == ((count_fun(0, len(s), s)) + ((1 if ((len(s)) > (0)) and (((s)[(len(s)) - (1)]) == (121)) else 0))))
    count = int(0) # type : int
    count = 0
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (len(s)):
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(s))))
        Invariant(count >= 0)
        Invariant(Forall(int, lambda d_0_i_: 
            (Implies(d_0_i_ >= 0 and d_0_i_ < len(s), count_fun(0, d_0_i_ + 1, s) == count_fun(0, d_0_i_, s) + (1 if is__vowel(s[d_0_i_]) else 0)), [[count_fun(0, d_0_i_ + 1, s)]])))
        Invariant((count) == (count_fun(0, d_1_i_, s)))
        Assert(count_fun(0, d_1_i_ + 1, s) == count_fun(0, d_1_i_, s) + (1 if is__vowel(s[d_1_i_]) else 0))
        if is__vowel((s)[d_1_i_]):
            count = (count) + (1)
        d_1_i_ = (d_1_i_) + (1)
    count = (count) + ((1 if ((len(s)) > (0)) and (((s)[(len(s)) - (1)]) == (121)) else 0))
    return count

@Pure
def count_fun(i : int, j : int, s : List[int]) -> int:
    Requires(Acc(list_pred(s)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(s))))
    Ensures((Result()) >= (0))
    if i == j:
        return 0
    else:
        if is__vowel((s)[j - 1]):
            return (1) + (count_fun(i, j - 1, s))
        else:
            return count_fun(i, j - 1, s)

@Pure
def is__vowel(c : int) -> bool :
    return ((((((((((c) == (97)) or ((c) == (101))) or ((c) == (105))) or ((c) == (111))) or ((c) == (117))) or ((c) == (65))) or ((c) == (69))) or ((c) == (73))) or ((c) == (79))) or ((c) == (85))
