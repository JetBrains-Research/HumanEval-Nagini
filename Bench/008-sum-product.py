from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return (s)[j - 1] + (psum(i, j - 1, s))
    # pure-end

@Pure
def prod(i : int, j : int, s : List[int]) -> int :
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

    # pure-start
    if i == j:
        return 1
    else:
        return (s)[j - 1] * (prod(i, j - 1, s))
    # pure-end

def sum__product(numbers : List[int]) -> Tuple[int, int]:
    # pre-conditions-start
    Requires(Acc(list_pred(numbers)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(numbers)))
    Ensures((Result()[0]) == (psum(0, len(numbers), numbers)))
    Ensures((Result()[1]) == (prod(0, len(numbers), numbers)))
    # post-conditions-end

    # impl-start
    s : int = 0
    p : int = 1
    d_2_i_ : int = 0
    while (d_2_i_) < (len(numbers)):
        # invariants-start
        Invariant(Acc(list_pred(numbers)))
        Invariant(((0) <= (d_2_i_)) and ((d_2_i_) <= (len(numbers))))
        Invariant((s) == (psum(0, d_2_i_, numbers)))
        Invariant(Forall(int, lambda d_2_i_: (not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(numbers)))) or ((psum(0, d_2_i_ + 1, numbers)) == (psum(0, d_2_i_, numbers) + numbers[d_2_i_])), [[psum(0, d_2_i_ + 1, numbers)]])))
        Invariant(Forall(int, lambda d_2_i_: (not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(numbers)))) or ((prod(0, d_2_i_ + 1, numbers)) == (prod(0, d_2_i_, numbers) * numbers[d_2_i_])), [[prod(0, d_2_i_ + 1, numbers)]])))
        Invariant((p) == (prod(0, d_2_i_, numbers)))
        # invariants-end

        # assert-start
        Assert((psum(0, (d_2_i_) + (1), numbers)) == ((psum(0, d_2_i_, numbers) + (numbers)[d_2_i_])))
        # assert-end
        s = (s) + ((numbers)[d_2_i_])
        # assert-start
        Assert((prod(0, d_2_i_ + 1, numbers)) == ((prod(0, d_2_i_, numbers)) * ((numbers)[d_2_i_])))
        # assert-end
        p = (p) * ((numbers)[d_2_i_])
        d_2_i_ = (d_2_i_) + (1)
    return s, p
    # impl-end
