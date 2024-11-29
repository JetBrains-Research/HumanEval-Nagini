from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def min(a : int, b : int) -> int :
    # pure-start
    if (a) <= (b):
        return a
    elif True:
        return b
    # pure-end

#use-as-unpure
@Pure
def max(a : int, b : int) -> int :
    # pure-start
    if (a) >= (b):
        return a
    elif True:
        return b
    # pure-end

def generate__integers(a : int, b : int) -> List[int]:
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(Result())))) or ((((Result())[d_0_i_] % 2)) == (0))))
    Ensures(Forall(int, lambda d_1_i_:
        not (((d_1_i_) >= (0)) and ((d_1_i_) < (len(Result())))) or (((Result())[d_1_i_]) > 0 and ((Result())[d_1_i_]) < 10)))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    d_2_left_ : int = min(a, b)
    d_3_right_ : int = max(a, b)
    d_4_lower_ : int = max(2, d_2_left_)
    d_5_upper_ : int = min(8, d_3_right_)
    d_6_i_ : int = d_4_lower_
    
    while (d_6_i_) <= (d_5_upper_):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(d_6_i_ >= 2)
        Invariant(Implies((d_6_i_) <= (d_5_upper_), d_6_i_ <= 8))
        Invariant(d_5_upper_ <= 8)
        Invariant(Forall(int, lambda d_7_i_:
            not (((d_7_i_) >= (0)) and ((d_7_i_) < (len(result)))) or ((((result)[d_7_i_] % 2)) == (0))))
        Invariant(Forall(int, lambda d_8_j_:
            (not (((d_8_j_) >= (0)) and ((d_8_j_) < (len(result)))) or (((result)[d_8_j_]) > 0 and ((result)[d_8_j_]) < 10), [[result[d_8_j_]]])))
        # invariants-end
        if ((d_6_i_ % 2)) == (0):
            result = (result) + (([d_6_i_]))
        d_6_i_ = (d_6_i_) + (1)
    return result
    # impl-end
