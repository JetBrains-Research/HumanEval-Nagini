from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def min(a : int, b : int) -> int:
    Ensures(((Result()) == (a)) or ((Result()) == (b)))
    Ensures(((Result()) <= (a)) and ((Result()) <= (b)))
    m = int(0) # type : int
    if (a) < (b):
        m = a
    elif True:
        m = b
    return m

@Pure
def max(a : int, b : int) -> int:
    Ensures(((Result()) == (a)) or ((Result()) == (b)))
    Ensures(((Result()) >= (a)) and ((Result()) >= (b)))
    m = int(0) # type : int
    if (a) > (b):
        m = a
    elif True:
        m = b
    return m

def generate__integers(a : int, b : int) -> List[int]:
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(Result())))) or ((((Result())[d_0_i_] % 2)) == (0))))
    Ensures(Forall(int, lambda d_1_i_:
        not (((d_1_i_) >= (0)) and ((d_1_i_) < (len(Result())))) or (((Result())[d_1_i_]) > 0 and ((Result())[d_1_i_]) < 10)))
    result = list([int(0)] * 0) # type : List[int]
    d_2_left_ = int(0) # type : int
    d_2_left_ = min(a, b)
    d_3_right_ = int(0) # type : int
    d_3_right_ = max(a, b)
    d_4_lower_ = int(0) # type : int
    d_4_lower_ = max(2, d_2_left_)
    d_5_upper_ = int(0) # type : int
    d_5_upper_ = min(8, d_3_right_)
    result = list([])
    d_6_i_ = int(0) # type : int
    d_6_i_ = d_4_lower_
    
    while (d_6_i_) <= (d_5_upper_):
        Invariant(Acc(list_pred(result)))
        Invariant(d_6_i_ >= 2)
        Invariant(Implies((d_6_i_) <= (d_5_upper_), d_6_i_ <= 8))
        Invariant(d_5_upper_ <= 8)
        Invariant(Forall(int, lambda d_7_i_:
            not (((d_7_i_) >= (0)) and ((d_7_i_) < (len(result)))) or ((((result)[d_7_i_] % 2)) == (0))))
        Invariant(Forall(int, lambda d_8_j_:
            (not (((d_8_j_) >= (0)) and ((d_8_j_) < (len(result)))) or (((result)[d_8_j_]) > 0 and ((result)[d_8_j_]) < 10), [[result[d_8_j_]]])))
        if ((d_6_i_ % 2)) == (0):
            result = (result) + (([d_6_i_]))
        d_6_i_ = (d_6_i_) + (1)
    return result