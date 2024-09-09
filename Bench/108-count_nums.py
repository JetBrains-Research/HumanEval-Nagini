from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def count__nums(s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Result() == get_positive(0, len(s), s))
    # post-conditions-end

    # impl-start
    cnt = int(0) # type : int
    cnt = 0
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(s))))
        Invariant(Forall(int, lambda x : 
            (Implies(0 <= x and x < len(s), get_positive(0, x + 1, s) == ((digits__sum(s[x]) > 0) + get_positive(0, x, s))), 
                [[get_positive(0, x + 1, s)]])))
        Invariant((cnt) == (get_positive(0, d_1_i_, s)))
        # invariants-end
        # assert-start
        Assert(get_positive(0, d_1_i_ + 1, s) == (digits__sum(s[d_1_i_]) > 0) + get_positive(0, d_1_i_, s))
        # assert-end
        if (digits__sum((s)[d_1_i_])) > (0):
            cnt = (cnt) + (1)
        d_1_i_ = (d_1_i_) + (1)
    return cnt
    # impl-end

@Pure 
def get_positive(i : int, j : int, s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

    # impl-start
    if i == j:
        return 0
    else:
        return (digits__sum(s[j - 1]) > 0) + get_positive(i, j - 1, s)
    # impl-end

@Pure
def digits__sum(x : int) -> int :
    # impl-start
    if abs(x) < 10:
        return x % 10
    else:
        return (10 - x % 10) + digits__sum(x // 10)
    # impl-end

@Pure
def abs(x : int) -> int :
    # pre-conditions-start
    Ensures((Result()) >= (0)) 
    Ensures((Result()) == (x) or (Result()) == (0) - (x))
    # pre-conditions-end

    # impl-start
    if (x) >= (0):
        return x
    elif True:
        return (0) - (x)
    # impl-end