from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def abs(x : int) -> int :
    # pure-start
    if (x) >= (0):
        return x
    elif True:
        return (0) - (x)
    # pure-end

@Pure
def sum__abs(i : int, j : int, s : List[int]) -> int :
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return abs(s[j - 1]) + sum__abs(i, j - 1, s)
    # pure-end
    
@Pure 
def count_negatives(i : int, j : int, s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return (1 if s[j - 1] < 0 else 0) + count_negatives(i, j - 1, s)
    # pure-end

def prod__signs(numbers : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(numbers)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(numbers)))
    Ensures((abs(Result())) == (sum__abs(0, len(numbers), numbers)))
    Ensures(Implies(count_negatives(0, len(numbers), numbers) % 2 == 1, Result() <= 0))
    Ensures(Implies(count_negatives(0, len(numbers), numbers) % 2 == 0, Result() >= 0))
    # post-conditions-end

    # impl-start
    s : int = 0
    d_3_i_ : int = 0
    while (d_3_i_) < (len(numbers)):
        # invariants-start
        Invariant(Acc(list_pred(numbers)))
        Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= (len(numbers))))
        Invariant(Forall(int, lambda x : 
            (Implies(0 <= x and x < len(numbers), sum__abs(0, x + 1, numbers) == sum__abs(0, x, numbers) + abs(numbers[x])), 
                [[sum__abs(0, x + 1, numbers)]])))
        Invariant((s) == (sum__abs(0, d_3_i_, numbers)))
        Invariant(s >= 0)
        # invariants-end

        # assert-start
        Assert(sum__abs(0, d_3_i_ + 1, numbers) == sum__abs(0, d_3_i_, numbers) + abs(numbers[d_3_i_]))
        # assert-end
        s = (s) + (abs((numbers)[d_3_i_]))
        d_3_i_ = (d_3_i_) + (1)
    d_3_i_ = 0
    d_4_cnt_ : int = 0
    while (d_3_i_) < (len(numbers)):
        # invariants-start
        Invariant(Acc(list_pred(numbers)))
        Invariant(s == sum__abs(0, len(numbers), numbers))
        Invariant(s >= 0)
        Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= (len(numbers))))
        Invariant(Forall(int, lambda x : Implies(0 <= x and x < len(numbers), count_negatives(0, x + 1, numbers) == count_negatives(0, x, numbers) + (1 if numbers[x] < 0 else 0))))
        Invariant((d_4_cnt_) == (count_negatives(0, d_3_i_, numbers)))
        # invariants-end
        if ((numbers)[d_3_i_]) < (0):
            d_4_cnt_ = (d_4_cnt_) + (1)
        d_3_i_ = (d_3_i_) + (1)
    if ((d_4_cnt_ % 2)) == (1):
        s = (0) - (s)
    return s
    # impl-end
