from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def HasNoEvenDigit(n : int) -> bool :
    Requires(((0) <= (n)))
    return (n == 0 or (((((n % 10) % 2)) != (0)) and (HasNoEvenDigit((n // 10)))))

def UniqueDigits(x : List[int]) -> List[int]:
    Requires(Acc(list_pred(x)))
    Requires(Forall(int, lambda d_0_i_: Implies(d_0_i_ >= 0 and d_0_i_ < len(x), (x[d_0_i_] >= 0))))
    Ensures(Acc(list_pred(x)))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_0_i_: Implies(d_0_i_ >= 0 and d_0_i_ < len(x), (x[d_0_i_] >= 0))))
    Ensures(Forall(int, lambda d_0_i_: Implies(d_0_i_ >= 0 and d_0_i_ < len(Result()), (Result()[d_0_i_] >= 0))))
    Ensures(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(Result())))) or (HasNoEvenDigit((Result())[d_0_i_]))))
    Ensures(Forall(int, lambda d_1_i_:
        Forall(int, lambda d_2_j_:
            not ((((0) <= (d_1_i_)) and ((d_1_i_) < (d_2_j_))) and ((d_2_j_) < (len(Result())))) or (((Result())[d_1_i_]) <= ((Result())[d_2_j_])))))
    Ensures(Forall(int, lambda d_8_e_:
        not (((d_8_e_) >= 0 and d_8_e_ < len(x)) and (HasNoEvenDigit(x[d_8_e_]))) or (Exists(int, lambda d_9_j_: (d_9_j_ >= 0 and d_9_j_ < len(result)) and result[d_9_j_] == x[d_8_e_]))))
    Ensures(Forall(int, lambda d_7_e_:
        not ((d_7_e_) >= 0 and d_7_e_ < len(result)) or (Exists(int, lambda d_8_j_: (d_8_j_ >= 0 and d_8_j_ < len(x)) and x[d_8_j_] == result[d_7_e_]))))
    result = list([int(0)] * 0) # type : List[int]
    result = list([])
    d_5_i_ = 0
    while d_5_i_ < len(x):
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(x)))
        Invariant(0 <= d_5_i_ and d_5_i_ <= len(x))
        Invariant(Forall(int, lambda d_0_i_: Implies(d_0_i_ >= 0 and d_0_i_ < len(x), (x[d_0_i_] >= 0))))
        Invariant(Forall(int, lambda d_0_i_: Implies(d_0_i_ >= 0 and d_0_i_ < len(result), (result[d_0_i_] >= 0))))
        Invariant(Forall(int, lambda d_6_j_:
            (Implies(((0) <= (d_6_j_)) and ((d_6_j_) < (len(result))), HasNoEvenDigit((result)[d_6_j_])), [[HasNoEvenDigit((result)[d_6_j_])]])))
        Invariant(Forall(int, lambda d_8_e_:
            Implies(((d_8_e_) >= 0 and d_8_e_ < d_5_i_) and (HasNoEvenDigit(x[d_8_e_])), Exists(int, lambda d_9_j_: (d_9_j_ >= 0 and d_9_j_ < len(result)) and result[d_9_j_] == x[d_8_e_]))))
        Invariant(Forall(int, lambda d_7_e_:
            Implies((d_7_e_) >= 0 and d_7_e_ < len(result), 
                (Exists(int, lambda d_8_j_: (d_8_j_ >= 0 and d_8_j_ < d_5_i_) and x[d_8_j_] == result[d_7_e_]), [[Exists(int, lambda d_8_j_: (d_8_j_ >= 0 and d_8_j_ < d_5_i_) and x[d_8_j_] == result[d_7_e_])]]))))
        if HasNoEvenDigit((x)[d_5_i_]):
            result = (result) + [(x)[d_5_i_]]
        d_5_i_ = (d_5_i_) + (1)
    d_9_i_ = int(0) # type : int
    d_9_i_ = 0
    while (d_9_i_) < (len(result)):
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(x)))
        Invariant(((0) <= (d_9_i_)) and ((d_9_i_) <= (len(result))))
        Invariant(Forall(int, lambda d_0_i_: Implies(d_0_i_ >= 0 and d_0_i_ < len(result), (result[d_0_i_] >= 0))))
        Invariant(Forall(int, lambda d_10_j_:
            Forall(int, lambda d_11_k_:
                not ((((0) <= (d_10_j_)) and ((d_10_j_) < (d_11_k_))) and ((d_11_k_) < (d_9_i_))) or (((result)[d_10_j_]) <= ((result)[d_11_k_])))))
        Invariant(Forall(int, lambda d_13_j_:
            not (((0) <= (d_13_j_)) and ((d_13_j_) < (d_9_i_))) or (Forall(int, lambda d_14_k_:
                not (((d_9_i_) <= (d_14_k_)) and ((d_14_k_) < (len(result)))) or (((result)[d_13_j_]) <= ((result)[d_14_k_]))))))
        Invariant(Forall(int, lambda d_0_i_: Implies(d_0_i_ >= 0 and d_0_i_ < len(x), (x[d_0_i_] >= 0))))
        Invariant(Forall(int, lambda d_0_i_: Implies(d_0_i_ >= 0 and d_0_i_ < len(result), (result[d_0_i_] >= 0))))
        Invariant(Forall(int, lambda d_6_j_:
            (Implies(((0) <= (d_6_j_)) and ((d_6_j_) < (len(result))), HasNoEvenDigit((result)[d_6_j_])), [[HasNoEvenDigit((result)[d_6_j_])]])))
        Invariant(Forall(int, lambda d_8_e_:
            Implies(((d_8_e_) >= 0 and d_8_e_ < d_5_i_) and (HasNoEvenDigit(x[d_8_e_])), Exists(int, lambda d_9_j_: (d_9_j_ >= 0 and d_9_j_ < len(result)) and result[d_9_j_] == x[d_8_e_]))))
        Invariant(Forall(int, lambda d_7_e_:
            Implies((d_7_e_) >= 0 and d_7_e_ < len(result), 
                (Exists(int, lambda d_8_j_: (d_8_j_ >= 0 and d_8_j_ < d_5_i_) and x[d_8_j_] == result[d_7_e_]), [[Exists(int, lambda d_8_j_: (d_8_j_ >= 0 and d_8_j_ < d_5_i_) and x[d_8_j_] == result[d_7_e_])]]))))
        d_17_minIndex_ = int(0) # type : int
        d_17_minIndex_ = d_9_i_
        d_18_j_ = int(0) # type : int
        d_18_j_ = (d_9_i_) + (1)
        while (d_18_j_) < (len(result)):
            Invariant(Acc(list_pred(result)))
            Invariant(((0) <= (d_9_i_)) and ((d_9_i_) < (len(result))))
            Invariant(Forall(int, lambda d_0_i_: Implies(d_0_i_ >= 0 and d_0_i_ < len(result), (result[d_0_i_] >= 0))))
            Invariant(Acc(list_pred(x)))
            Invariant((((d_9_i_) <= (d_17_minIndex_)) and ((d_17_minIndex_) < (d_18_j_))) and ((d_18_j_) <= (len(result))))
            Invariant(Forall(int, lambda d_19_k_:
                not (((d_9_i_) <= (d_19_k_)) and ((d_19_k_) < (d_18_j_))) or (((result)[d_17_minIndex_]) <= ((result)[d_19_k_]))))
            if ((result)[d_18_j_]) < ((result)[d_17_minIndex_]):
                d_17_minIndex_ = d_18_j_
            d_18_j_ = (d_18_j_) + (1)
        if (d_17_minIndex_) != (d_9_i_):
            d_20_temp_ = int(0) # type : int
            d_20_temp_ = (result)[d_9_i_]
            result[d_9_i_] = (result)[d_17_minIndex_]
            result[d_17_minIndex_] = d_20_temp_
        d_9_i_ = (d_9_i_) + (1)
    return result