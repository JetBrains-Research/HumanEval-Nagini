from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def vowel__count(s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) >= (0))
    Ensures(Result() == ((count_fun(0, len(s), s)) + ((1 if ((len(s)) > (0)) and (((s)[(len(s)) - (1)]) == (121)) else 0))))
    # post-conditions-end

    # impl-start
    count : int = 0
    d_1_i_ : int = 0
    while (d_1_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(s))))
        Invariant(count >= 0)
        Invariant(Forall(int, lambda d_0_i_: 
            (Implies(d_0_i_ >= 0 and d_0_i_ < len(s), count_fun(0, d_0_i_ + 1, s) == count_fun(0, d_0_i_, s) + (1 if is__vowel(s[d_0_i_]) else 0)), [[count_fun(0, d_0_i_ + 1, s)]])))
        Invariant((count) == (count_fun(0, d_1_i_, s)))
        # invariants-end
        # assert-start
        Assert(count_fun(0, d_1_i_ + 1, s) == count_fun(0, d_1_i_, s) + (1 if is__vowel(s[d_1_i_]) else 0))
        # assert-end
        if is__vowel((s)[d_1_i_]):
            count = (count) + (1)
        d_1_i_ = (d_1_i_) + (1)
    count = (count) + ((1 if ((len(s)) > (0)) and (((s)[(len(s)) - (1)]) == (121)) else 0))
    return count
    # impl-end

@Pure
def count_fun(i : int, j : int, s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(s))))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) >= (0))
    # post-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        if is__vowel((s)[j - 1]):
            return (1) + (count_fun(i, j - 1, s))
        else:
            return count_fun(i, j - 1, s)
    # pure-end

@Pure
def is__vowel(c : int) -> bool :
    # pure-start
    return ((((((((((c) == (97)) or ((c) == (101))) or ((c) == (105))) or ((c) == (111))) or ((c) == (117))) or ((c) == (65))) or ((c) == (69))) or ((c) == (73))) or ((c) == (79))) or ((c) == (85))
    # pure-end
