from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def sorted__even(a : List[int]) -> List[int]:
    Requires(Acc(list_pred(a)))
    Requires((len(a)) > (0))
    Ensures(Acc(list_pred(a)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (len(a)))
    Ensures(Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            not ((((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len(Result())))) and (((d_0_i_ % 2)) == (0))) and (((d_1_j_ % 2)) == (0))) or (((Result())[d_0_i_]) <= ((Result())[d_1_j_])))))
    Ensures(Forall(int, lambda d_2_i_:
        not ((((0) <= (d_2_i_)) and ((d_2_i_) < (len(a)))) and (((d_2_i_ % 2)) == (1))) or (((Result())[d_2_i_]) == ((a)[d_2_i_]))))
    sorted__even = list([int(0)] * 0) # type : List[int]
    d_3_p_ = list([False] * 0) # type : List[bool]
    d_3_p_ = list([])
    d_4_i_ = int(0) # type : int
    d_4_i_ = 0
    while (d_4_i_) < (len(a)):
        Invariant(Acc(list_pred(d_3_p_)))
        Invariant(Acc(list_pred(sorted__even)))
        Invariant(Acc(list_pred(a)))
        Invariant(((0) <= (d_4_i_)) and ((d_4_i_) <= (len(a))))
        Invariant((len(d_3_p_)) == (d_4_i_))
        Invariant(Forall(int, lambda d_5_j_:
            not (((0) <= (d_5_j_)) and ((d_5_j_) < (d_4_i_))) or (((d_3_p_)[d_5_j_]) == (((d_5_j_ % 2)) == (0)))))
        d_3_p_ = (d_3_p_) + [((d_4_i_ % 2)) == (0)]
        d_4_i_ = (d_4_i_) + (1)
    sorted__even = SortSeqPred(a, d_3_p_)
    return sorted__even

def SortSeqPred(s : List[int], p : List[bool]) -> List[int]:
    Requires(Acc(list_pred(p), 1/2))
    Requires(Acc(list_pred(s), 1/2))
    Requires((len(s)) == (len(p)))
    Ensures(Acc(list_pred(p), 1/2))
    Ensures(Acc(list_pred(s), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(s)) == (len(p)))
    Ensures((len(Result())) == (len(s)))
    Ensures(Forall(int, lambda d_6_i_:
        Forall(int, lambda d_7_j_:
            not ((((((0) <= (d_6_i_)) and ((d_6_i_) < (d_7_j_))) and ((d_7_j_) < (len(Result())))) and ((p)[d_6_i_])) and ((p)[d_7_j_])) or (((Result())[d_6_i_]) <= ((Result())[d_7_j_])))))
    Ensures(Forall(int, lambda d_8_i_:
        not ((((0) <= (d_8_i_)) and ((d_8_i_) < (len(s)))) and (not((p)[d_8_i_]))) or (((Result())[d_8_i_]) == ((s)[d_8_i_]))))
    sorted = list([int(0)] * 0) # type : List[int]
    sorted = list(s)
    d_9_i_ = int(0) # type : int
    d_9_i_ = 0
    while (d_9_i_) < (len(sorted)):
        Invariant(Acc(list_pred(sorted)))
        Invariant(Acc(list_pred(p), 1/2))
        Invariant(Acc(list_pred(s), 1/2))
        Invariant((len(s)) == (len(p)))
        Invariant(((0) <= (d_9_i_)) and ((d_9_i_) <= (len(sorted))))
        Invariant((len(sorted)) == (len(s)))
        Invariant(Forall(int, lambda d_14_j_:
            not ((((0) <= (d_14_j_)) and ((d_14_j_) < (len(s)))) and (not((p)[d_14_j_]))) or (((sorted)[d_14_j_]) == ((s)[d_14_j_]))))
        Invariant(Forall(int, lambda d_10_j_:
            (Forall(int, lambda d_11_k_:
                (not ((((((0) <= (d_10_j_)) and ((d_10_j_) < (d_11_k_))) and ((d_11_k_) < (d_9_i_))) and ((p)[d_10_j_])) and ((p)[d_11_k_])) or 
                (((sorted)[d_10_j_]) <= ((sorted)[d_11_k_])), [[(sorted)[d_11_k_]]])), [[sorted[d_10_j_]]])))
        Invariant(Forall(int, lambda d_12_j_:
            (not ((((0) <= (d_12_j_)) and ((d_12_j_) < (d_9_i_))) and ((p)[d_12_j_])) or 
                (Forall(int, lambda d_13_k_:
                    (not ((((d_9_i_) <= (d_13_k_)) and ((d_13_k_) < (len(sorted)))) and ((p)[d_13_k_])) or 
                        (((sorted)[d_12_j_]) <= ((sorted)[d_13_k_])), [[sorted[d_13_k_]]]))), [[(sorted)[d_12_j_]]])))
        if (p)[d_9_i_]:
            d_15_minIndex_ = int(0) # type : int
            d_15_minIndex_ = d_9_i_
            d_16_j_ = int(0) # type : int
            d_16_j_ = (d_9_i_) + (1)
            while (d_16_j_) < (len(sorted)):
                Invariant(Acc(list_pred(sorted)))
                Invariant(Acc(list_pred(p), 1/2))
                Invariant(Acc(list_pred(s), 1/2))
                Invariant((len(s)) == (len(p)))
                Invariant((len(sorted)) == (len(s)))
                Invariant(0 <= d_9_i_ and d_9_i_ < len(sorted))
                Invariant((((d_9_i_) <= (d_15_minIndex_)) and ((d_15_minIndex_) < (d_16_j_))) and ((d_16_j_) <= (len(sorted))))
                Invariant(p[d_9_i_])
                Invariant((p)[d_15_minIndex_])
                Invariant(Forall(int, lambda d_17_k_:
                    not ((((d_9_i_) <= (d_17_k_)) and ((d_17_k_) < (d_16_j_))) and ((p)[d_17_k_])) or (((sorted)[d_15_minIndex_]) <= ((sorted)[d_17_k_]))))
                Invariant(Forall(int, lambda d_14_j_:
                    not ((((0) <= (d_14_j_)) and ((d_14_j_) < (len(s)))) and (not((p)[d_14_j_]))) or (((sorted)[d_14_j_]) == ((s)[d_14_j_]))))
                Invariant(Forall(int, lambda d_10_j_:
                    (Forall(int, lambda d_11_k_:
                        (not ((((((0) <= (d_10_j_)) and ((d_10_j_) < (d_11_k_))) and ((d_11_k_) < (d_9_i_))) and ((p)[d_10_j_])) and ((p)[d_11_k_])) or 
                        (((sorted)[d_10_j_]) <= ((sorted)[d_11_k_])), [[(sorted)[d_11_k_]]])), [[sorted[d_10_j_]]])))
                Invariant(Forall(int, lambda d_12_j_:
                    (not ((((0) <= (d_12_j_)) and ((d_12_j_) < (d_9_i_))) and ((p)[d_12_j_])) or 
                        (Forall(int, lambda d_13_k_:
                            (not ((((d_9_i_) <= (d_13_k_)) and ((d_13_k_) < (len(sorted)))) and ((p)[d_13_k_])) or 
                                (((sorted)[d_12_j_]) <= ((sorted)[d_13_k_])), [[sorted[d_13_k_]]]))), [[(sorted)[d_12_j_]]])))
                if ((p)[d_16_j_]) and (((sorted)[d_16_j_]) < ((sorted)[d_15_minIndex_])):
                    d_15_minIndex_ = d_16_j_
                d_16_j_ = (d_16_j_) + (1)
            if (d_15_minIndex_) != (d_9_i_):
                Assert((p)[d_15_minIndex_])
                Assert(p[d_9_i_])
                rhs0_ = (sorted)[d_9_i_] # type : int
                (sorted)[d_9_i_] = (sorted)[d_15_minIndex_]
                (sorted)[d_15_minIndex_] = rhs0_
        d_9_i_ = (d_9_i_) + (1)
    return sorted