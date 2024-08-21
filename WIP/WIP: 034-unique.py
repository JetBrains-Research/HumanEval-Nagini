from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def uniqueSorted(s : List[int]) -> List[int]:
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len(s))), 
                ((s)[d_0_i_]) <= ((s)[d_1_j_])))))
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    # Ensures(Forall(int, lambda d_2_i_:
    #     Forall(int, lambda d_3_j_:
    #         not ((((0) <= (d_2_i_)) and ((d_2_i_) < (d_3_j_))) and ((d_3_j_) < (len(Result())))) or (((Result())[d_2_i_]) < ((Result())[d_3_j_])))))
    # Ensures(Forall(int, lambda d_4_x_:
    #     not ((d_4_x_) in (Result())) or ((d_4_x_) in (s))))
    # Ensures(Forall(int, lambda d_5_x_:
    #     not ((d_5_x_) in (s)) or ((d_5_x_) in (Result()))))
    result = list([int(0)] * 0) # type : List[int]
    result = list([])
    d_6_i_ = int(0) # type : int
    d_6_i_ = 0
    while (d_6_i_) < (len(s)):
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(s), 1/2))
        Invariant(Forall(int, lambda d_0_i_:
            Forall(int, lambda d_1_j_:
                Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len(s))), 
                    ((s)[d_0_i_]) <= ((s)[d_1_j_])))))
        Invariant(((0) <= (d_6_i_)) and ((d_6_i_) <= (len(s))))
        # Invariant(Forall(int, lambda d_7_k_:
        #     Forall(int, lambda d_8_l_:
        #         not ((((0) <= (d_7_k_)) and ((d_7_k_) < (d_8_l_))) and ((d_8_l_) < (len(result)))) or (((result)[d_7_k_]) < ((result)[d_8_l_])))))
        Invariant(Forall(int, lambda d_9_k_:
            (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(result))), Exists(int, lambda d_10_m_:
                (((0) <= (d_10_m_)) and ((d_10_m_) < (d_6_i_))) and (((result)[d_9_k_]) == ((s)[d_10_m_])))), [[(result)[d_9_k_]]])))
        # Invariant(Forall(int, lambda d_11_k_:
        #     (Forall(int, lambda d_12_l_:
        #         (Implies(0 <= d_11_k_ and d_11_k_ < len(result), 
        #             Implies(d_6_i_ <= d_12_l_ and d_12_l_ < len(s), result[d_11_k_] <= s[d_12_l_])), 
        #             [[s[d_12_l_]]])), [[result[d_11_k_]]])))
        # Invariant(Forall(int, lambda d_11_j_:
        #     not (((0) <= (d_11_j_)) and ((d_11_j_) < (d_6_i_))) or (((s)[d_11_j_]) in (result))))
        if ((len(result)) == (0)) or (((result)[(len(result)) - (1)]) != ((s)[d_6_i_])):
            # Assert(((len(result)) == (0)) or (((result)[(len(result)) - (1)]) < ((s)[d_6_i_])))
            old_res = list(result)
            Assert(Forall(int, lambda d_9_k_:
                (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(result))), Exists(int, lambda d_10_m_:
                    (((0) <= (d_10_m_)) and ((d_10_m_) < (d_6_i_))) and (((result)[d_9_k_]) == ((s)[d_10_m_])))), [[(result)[d_9_k_]]])))
            Assert(Forall(int, lambda d_9_k_: Implies(0 <= d_9_k_ and d_9_k_ < len(result), result[d_9_k_] == old_res[d_9_k_])))
            Assert(Forall(int, lambda d_9_k_:
                (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(old_res))), Exists(int, lambda d_10_m_:
                    (((0) <= (d_10_m_)) and ((d_10_m_) < (d_6_i_))) and (((old_res)[d_9_k_]) == ((s)[d_10_m_])))), [[(old_res)[d_9_k_]]])))    
            result = (result) + [(s)[d_6_i_]]
            Assert(Exists(int, lambda d_10_m_:
                (((0) <= (d_10_m_)) and ((d_10_m_) <= (d_6_i_))) and (((result)[len(result) - 1]) == ((s)[d_10_m_]))))
            Assert(Forall(int, lambda d_9_k_:
                (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(old_res))), Exists(int, lambda d_10_m_:
                    (((0) <= (d_10_m_)) and ((d_10_m_) < (d_6_i_))) and (((old_res)[d_9_k_]) == ((s)[d_10_m_])))), [[(old_res)[d_9_k_]]])))    
            # Assert(Forall(int, lambda d_9_k_:
            #     (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(old_res))), Exists(int, lambda d_10_m_:
            #         (((0) <= (d_10_m_)) and ((d_10_m_) <= (d_6_i_))) and (((old_res)[d_9_k_]) == ((s)[d_10_m_])))), [[(old_res)[d_9_k_]]])))    
            # Assert(Forall(int, lambda d_9_k_:
            #     (Implies(((0) <= (d_9_k_)) and ((d_9_k_) + 1 < (len(result))), Exists(int, lambda d_10_m_:
            #         (((0) <= (d_10_m_)) and ((d_10_m_) <= (d_6_i_))) and (((result)[d_9_k_]) == ((s)[d_10_m_])))), [[(result)[d_9_k_]]])))    
            # Assert(Forall(int, lambda d_9_k_:
            #     (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(result))), Exists(int, lambda d_10_m_:
            #         (((0) <= (d_10_m_)) and ((d_10_m_) <= (d_6_i_))) and (((result)[d_9_k_]) == ((s)[d_10_m_])))), [[(result)[d_9_k_]]])))    
        d_6_i_ = (d_6_i_) + (1)
    return result

# def unique(s : List[int]) -> List[int]:
#     Requires(Acc(list_pred(s)))
#     Ensures(Acc(list_pred(s)))
#     Ensures(Acc(list_pred(Result())))
#     Ensures(Forall(int, lambda d_12_i_:
#         Forall(int, lambda d_13_j_:
#             not ((((0) <= (d_12_i_)) and ((d_12_i_) < (d_13_j_))) and ((d_13_j_) < (len(Result())))) or (((Result())[d_12_i_]) < ((Result())[d_13_j_])))))
#     Ensures(Forall(int, lambda d_14_x_:
#         not ((d_14_x_) in (Result())) or ((d_14_x_) in (s))))
#     Ensures(Forall(int, lambda d_15_x_:
#         not ((d_15_x_) in (s)) or ((d_15_x_) in (Result()))))
#     result = list([int(0)] * 0) # type : List[int]
#     d_16_sorted_ = list([int(0)] * 0) # type : List[int]
#     out0_ # type : List[int]
#     out0_ = BubbleSort(s)
#     d_16_sorted_ = out0_
#     out1_ # type : List[int]
#     out1_ = uniqueSorted(d_16_sorted_)
#     result = out1_
#     Assert(Forall(int, lambda d_17_x_:
#         not ((d_17_x_) in (d_16_sorted_)) or ((d_17_x_) in (s))))
#     Assert(Forall(int, lambda d_18_x_:
#         not ((d_18_x_) in (s)) or ((d_18_x_) in (d_16_sorted_))))
#     return result

def BubbleSort(a1 : List[int]) -> List[int]:
    Requires(Acc(list_pred(a1), 1/2))
    Ensures(Acc(list_pred(a1), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(a1)) == (len(Result())))
    # Ensures(ToMS(ToSeq(a1)) == ToMS(ToSeq(Result())))
    Ensures(Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len((Result())))), ((Result())[d_0_i_]) <= ((Result())[d_1_j_])))))
    a = list(a1) # type : List[int]
    d_2_i_ = int(0) # type : int
    d_2_i_ = (len((a))) - (1)
    while (d_2_i_) > (0):
        Invariant(Acc(list_pred(a)))
        Invariant(Acc(list_pred(a1), 1/2))
        Invariant((len(a1)) == (len(a)))
        Invariant(not ((d_2_i_) < (0)) or ((len((a))) == (0)))
        Invariant(((-1) <= (d_2_i_)) and ((d_2_i_) < (len((a)))))
        Invariant(Forall(int, lambda d_3_ii_:
            (Forall(int, lambda d_4_jj_:
                (Implies((((d_2_i_) <= (d_3_ii_)) and ((d_3_ii_) < (d_4_jj_))) and ((d_4_jj_) < (len((a)))), ((a)[d_3_ii_]) <= ((a)[d_4_jj_])),
                    [[(a)[d_4_jj_]]])),
                [[(a)[d_3_ii_]]])))
        Invariant(Forall(int, lambda d_5_k_:
            (Forall(int, lambda d_6_k_k_:
                (Implies(((((0) <= (d_5_k_)) and ((d_5_k_) <= (d_2_i_))) and ((d_2_i_) < (d_6_k_k_)) and (d_6_k_k_) < (len((a)))), ((a)[d_5_k_]) <= ((a)[d_6_k_k_])),
                    [[(a)[d_6_k_k_]]])),
                [[(a)[d_5_k_]]])))
        d_7_j_ = int(0) # type : int
        d_7_j_ = 0
        while (d_7_j_) < (d_2_i_):
            Invariant(Acc(list_pred(a)))
            Invariant(Acc(list_pred(a1), 1/2))
            Invariant((len(a1)) == (len(a)))
            Invariant((((0) < (d_2_i_)) and ((d_2_i_) < (len((a))))) and (((0) <= (d_7_j_)) and ((d_7_j_) <= (d_2_i_))))
            Invariant(Forall(int, lambda d_8_ii_:
                (Forall(int, lambda d_9_jj_:
                    (Implies((((d_2_i_) <= (d_8_ii_)) and ((d_8_ii_) <= (d_9_jj_))) and ((d_9_jj_) < (len((a)))), ((a)[d_8_ii_]) <= ((a)[d_9_jj_])),
                        [[(a)[d_9_jj_]]])),
                    [[(a)[d_8_ii_]]])))
            Invariant(Forall(int, lambda d_10_k_:
                (Forall(int, lambda d_11_k_k_:
                    (Implies(((((0) <= (d_10_k_)) and ((d_10_k_) <= (d_2_i_))) and ((d_2_i_) < (d_11_k_k_))) and ((d_11_k_k_) < (len((a)))), ((a)[d_10_k_]) <= ((a)[d_11_k_k_])),
                        [[(a)[d_11_k_k_]]])),
                    [[(a)[d_10_k_]]])))
            Invariant(Forall(int, lambda d_12_k_:
                (Implies(((0) <= (d_12_k_)) and ((d_12_k_) <= (d_7_j_)), ((a)[d_12_k_]) <= ((a)[d_7_j_])),
                    [[(a)[d_12_k_]]])))
            if ((a)[d_7_j_]) > ((a)[(d_7_j_) + (1)]):
                rhs0_ = (a)[(d_7_j_) + (1)] # type : int
                (a)[(d_7_j_) + (1)] = (a)[d_7_j_]
                (a)[d_7_j_] = rhs0_
            d_7_j_ = (d_7_j_) + (1)
        d_2_i_ = (d_2_i_) - (1)
    return a
