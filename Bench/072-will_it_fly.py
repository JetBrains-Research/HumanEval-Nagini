from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def will__it__fly(s : List[int], w : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires((len(s)) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == ((is__palindrome__pred(s)) and ((psum(0, len(s), s)) <= (w))))
    # post-conditions-end

    # impl-start
    result : bool = True
    d_0_i_ : int = 0
    d_1_j_ : int = (len(s)) - (1)
    while (d_0_i_) < (d_1_j_):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_0_i_)) and ((d_0_i_) < (len(s))))
        Invariant(((0) <= (d_1_j_)) and ((d_1_j_) < (len(s))))
        Invariant((d_1_j_) == (((len(s)) - (d_0_i_)) - (1)))
        Invariant(Forall(int, lambda d_2_k_:
            not (((0) <= (d_2_k_)) and ((d_2_k_) < (d_0_i_))) or (((s)[d_2_k_]) == ((s)[((len(s)) - (1)) - (d_2_k_)]))))
        # invariants-end
        if ((s)[d_0_i_]) != ((s)[d_1_j_]):
            result = False
            return result
        d_0_i_ = (d_0_i_) + (1)
        d_1_j_ = (d_1_j_) - (1)
    d_3_total_ : int = 0
    d_0_i_ = 0
    while (d_0_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_0_i_)) and ((d_0_i_) <= (len(s))))
        Invariant(Forall(int, lambda d_2_i_: (not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(s)))) or ((psum(0, d_2_i_ + 1, s)) == (psum(0, d_2_i_, s) + s[d_2_i_])), [[psum(0, d_2_i_ + 1, s)]])))
        Invariant((d_3_total_) == (psum(0, d_0_i_, s)))
        Invariant(Forall(int, lambda d_2_k_:
            not (((0) <= (d_2_k_)) and ((d_2_k_) < (len(s)))) or (((s)[d_2_k_]) == ((s)[((len(s)) - (1)) - (d_2_k_)]))))
        # invariants-end

        # assert-start
        Assert((psum(0, (d_0_i_) + (1), s)) == ((psum(0, d_0_i_, s) + (s)[d_0_i_])))
        # assert-end
        d_3_total_ = (d_3_total_) + ((s)[d_0_i_])
        d_0_i_ = (d_0_i_) + (1)
    return (d_3_total_) <= (w)
    # impl-end

@Pure
def is__palindrome__pred(s : List[int]) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end

    # pure-start
    return Forall(int, lambda d_4_k_:
        not (((0) <= (d_4_k_)) and ((d_4_k_) < (len(s)))) or (((s)[d_4_k_]) == ((s)[((len(s)) - (1)) - (d_4_k_)])))
    # pure-end

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
