from typing import List
from nagini_contracts.contracts import *

def remove__vowels(text : List[int]) -> List[int]:
    Requires(Acc(list_pred(text)))
    Ensures(Acc(list_pred(text)))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(Result())))) or (((((((Result())[d_0_i_]) != (0)) and (((Result())[d_0_i_]) != (1))) and (((Result())[d_0_i_]) != (2))) and (((Result())[d_0_i_]) != (3))) and (((Result())[d_0_i_]) != (4)))))
    Ensures(Forall(int, lambda d_1_i_:
        not (((d_1_i_) >= (0)) and ((d_1_i_) < (len(Result())))) or (((Result())[d_1_i_]) in (text))))
    Ensures(Forall(int, lambda d_2_j_:
        not ((((((((d_2_j_) >= (0)) and ((d_2_j_) < (len(text)))) and (((text)[d_2_j_]) != (0))) and (((text)[d_2_j_]) != (1))) and (((text)[d_2_j_]) != (2))) and (((text)[d_2_j_]) != (3))) and (((text)[d_2_j_]) != (4))) or (((text)[d_2_j_]) in (Result()))))
    s = list([int(0)] * 0) # type : List[int]
    s = []
    d_3_i_ = int(0) # type : int
    d_3_i_ = 0
    while (d_3_i_) < (len(text)):
        Invariant(Acc(list_pred(text)))
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= (len(text))))
        Invariant(Forall(int, lambda d_4_i_:
            not (((d_4_i_) >= (0)) and ((d_4_i_) < (len(s)))) or (((((((s)[d_4_i_]) != (0)) and (((s)[d_4_i_]) != (1))) and (((s)[d_4_i_]) != (2))) and (((s)[d_4_i_]) != (3))) and (((s)[d_4_i_]) != (4)))))
        Invariant(Forall(int, lambda d_5_i_:
            not (((d_5_i_) >= (0)) and ((d_5_i_) < (len(s)))) or (((s)[d_5_i_]) in (text))))
        Invariant(Forall(int, lambda d_6_j_:
            not ((((((((d_6_j_) >= (0)) and ((d_6_j_) < (d_3_i_))) and (((text)[d_6_j_]) != (0))) and (((text)[d_6_j_]) != (1))) and (((text)[d_6_j_]) != (2))) and (((text)[d_6_j_]) != (3))) and (((text)[d_6_j_]) != (4))) or (((text)[d_6_j_]) in (s))))
        d_7_c_ = (text)[d_3_i_] # type : int
        if (((((d_7_c_) != (0)) and ((d_7_c_) != (1))) and ((d_7_c_) != (2))) and ((d_7_c_) != (3))) and ((d_7_c_) != (4)):
            s = (s) + [d_7_c_]
        d_3_i_ = (d_3_i_) + (1)
    return s
