from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def count__nums(s : List[int]) -> int:
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(s)))
    Ensures(Result() == get_positive(0, len(s), s))
    cnt = int(0) # type : int
    cnt = 0
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (len(s)):
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(s))))
        Invariant(Forall(int, lambda x : 
            (Implies(0 <= x and x < len(s), get_positive(0, x + 1, s) == ((digits__sum(s[x]) > 0) + get_positive(0, x, s))), 
                [[get_positive(0, x + 1, s)]])))
        Invariant((cnt) == (get_positive(0, d_1_i_, s)))
        Assert(get_positive(0, d_1_i_ + 1, s) == (digits__sum(s[d_1_i_]) > 0) + get_positive(0, d_1_i_, s))
        if (digits__sum((s)[d_1_i_])) > (0):
            cnt = (cnt) + (1)
        d_1_i_ = (d_1_i_) + (1)
    return cnt

@Pure 
def get_positive(i : int, j : int, s : List[int]) -> int:
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    if i == j:
        return 0
    else:
        return (digits__sum(s[j - 1]) > 0) + get_positive(i, j - 1, s)

@Pure
def digits__sum(x : int) -> int :
    if abs(x) < 10:
        return x % 10
    else:
        return (10 - x % 10) + digits__sum(x // 10)

@Pure
def abs(x : int) -> int :
    Ensures((Result()) >= (0)) 
    Ensures((Result()) == (x) or (Result()) == (0) - (x))
    if (x) >= (0):
        return x
    elif True:
        return (0) - (x)