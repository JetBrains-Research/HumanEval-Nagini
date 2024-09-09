from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def monotonic(xs : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(xs)))
    Requires((len(xs)) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(xs)))
    Ensures((Result()) == ((Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            not ((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len(xs)))) or (((xs)[d_0_i_]) < ((xs)[d_1_j_]))))) or (Forall(int, lambda d_2_i_:
        Forall(int, lambda d_3_j_:
            not ((((0) <= (d_2_i_)) and ((d_2_i_) < (d_3_j_))) and ((d_3_j_) < (len(xs)))) or (((xs)[d_2_i_]) > ((xs)[d_3_j_])))))))
    # post-conditions-end

    # impl-start
    result = False # type : bool
    if (len(xs)) == (1):
        result = True
        return result
    d_4_increasing_ = False # type : bool
    d_4_increasing_ = True
    d_5_decreasing_ = False # type : bool
    d_5_decreasing_ = True
    d_6_i_ = int(0) # type : int
    d_6_i_ = 1
    while (d_6_i_) < (len(xs)):
        # invariants-start
        Invariant(Acc(list_pred(xs)))
        Invariant(((1) <= (d_6_i_)) and ((d_6_i_) <= (len(xs))))
        Invariant((d_4_increasing_) == (Forall(int, lambda d_7_j_:
            Forall(int, lambda d_8_k_:
                not ((((0) <= (d_7_j_)) and ((d_7_j_) < (d_8_k_))) and ((d_8_k_) < (d_6_i_))) or (((xs)[d_7_j_]) < ((xs)[d_8_k_]))))))
        Invariant((d_5_decreasing_) == (Forall(int, lambda d_9_j_:
            Forall(int, lambda d_10_k_:
                not ((((0) <= (d_9_j_)) and ((d_9_j_) < (d_10_k_))) and ((d_10_k_) < (d_6_i_))) or (((xs)[d_9_j_]) > ((xs)[d_10_k_]))))))
        # invariants-end
        if ((xs)[(d_6_i_) - (1)]) >= ((xs)[d_6_i_]):
            d_4_increasing_ = False
        if ((xs)[(d_6_i_) - (1)]) <= ((xs)[d_6_i_]):
            d_5_decreasing_ = False
        d_6_i_ = (d_6_i_) + (1)
    result = (d_4_increasing_) or (d_5_decreasing_)
    return result
    # impl-end