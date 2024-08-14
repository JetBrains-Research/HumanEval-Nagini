from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    if i == j:
        return 0
    else:
        return (s)[j - 1] + (psum(i, j - 1, s))

@Pure
def prod(i : int, j : int, s : List[int]) -> int :
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    if i == j:
        return 1
    else:
        return (s)[j - 1] * (prod(i, j - 1, s))

def sum__product(numbers : List[int]) -> Tuple[int, int]:
    Requires(Acc(list_pred(numbers)))
    Ensures(Acc(list_pred(numbers)))
    Ensures((Result()[0]) == (psum(0, len(numbers), numbers)))
    Ensures((Result()[1]) == (prod(0, len(numbers), numbers)))
    s = int(0) # type : int
    p = int(0) # type : int
    s = 0
    p = 1
    d_2_i_ = int(0) # type : int
    d_2_i_ = 0
    while (d_2_i_) < (len(numbers)):
        Invariant(Acc(list_pred(numbers)))
        Invariant(((0) <= (d_2_i_)) and ((d_2_i_) <= (len(numbers))))
        Invariant((s) == (psum(0, d_2_i_, numbers)))
        Invariant(Forall(int, lambda d_2_i_: (not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(numbers)))) or ((psum(0, d_2_i_ + 1, numbers)) == (psum(0, d_2_i_, numbers) + numbers[d_2_i_])), [[psum(0, d_2_i_ + 1, numbers)]])))
        Invariant(Forall(int, lambda d_2_i_: (not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(numbers)))) or ((prod(0, d_2_i_ + 1, numbers)) == (prod(0, d_2_i_, numbers) * numbers[d_2_i_])), [[prod(0, d_2_i_ + 1, numbers)]])))
        Invariant((p) == (prod(0, d_2_i_, numbers)))
        Assert((psum(0, (d_2_i_) + (1), numbers)) == ((psum(0, d_2_i_, numbers) + (numbers)[d_2_i_])))
        s = (s) + ((numbers)[d_2_i_])
        Assert((prod(0, d_2_i_ + 1, numbers)) == ((prod(0, d_2_i_, numbers)) * ((numbers)[d_2_i_])))
        p = (p) * ((numbers)[d_2_i_])
        d_2_i_ = (d_2_i_) + (1)
    return s, p