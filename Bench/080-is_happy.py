from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def ThreeDistinct(s : List[int], i : int) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(((0) < (i)) and ((i) < ((len(s)) - (1))))
    # pre-conditions-end

    # pure-start
    return ((((s)[(i) - (1)]) != ((s)[i])) and (((s)[i]) != ((s)[(i) + (1)]))) and (((s)[(i) - (1)]) != ((s)[(i) + (1)]))
    # pure-end

@Pure
def Happy(s : List[int]) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end

    # pure-start
    return ((len(s)) >= (3)) and (Forall(int, lambda d_0_i_:
        Implies(((0) < (d_0_i_)) and ((d_0_i_) < ((len(s)) - (1))), ThreeDistinct(s, d_0_i_))))
    # pure-end

def IsHappy(s : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == (Happy(s)))
    # post-conditions-end

    # impl-start
    if (len(s)) < (3):
        return False
    d_1_i_ : int = 1
    while (d_1_i_) < ((len(s)) - (1)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) < (d_1_i_)) and ((d_1_i_) <= ((len(s)) - (1))))
        Invariant(len(s) >= 3)
        Invariant(Forall(int, lambda d_2_j_:
            Implies(((0) < (d_2_j_)) and ((d_2_j_) < (d_1_i_)), ThreeDistinct(s, d_2_j_))))
        # invariants-end
        if not(ThreeDistinct(s, d_1_i_)):
            return False
        d_1_i_ = (d_1_i_) + (1)
    return True
    # impl-end
