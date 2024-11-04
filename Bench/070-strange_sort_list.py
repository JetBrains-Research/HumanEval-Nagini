from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def strange__sort__list__helper(s : List[int]) -> Tuple[List[int], List[int]]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result()[0])))
    Ensures(Acc(list_pred(Result()[1])))
    Ensures(Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len((Result()[0])))), ((Result()[0])[d_0_i_]) <= ((Result()[0])[d_1_j_])))))
    Ensures(((len(s)) == (len(Result()[0]))) and ((len(Result()[0])) == (len(Result()[1]))))
    Ensures(Forall(int, lambda d_0_i_:
        not ((((0) <= (d_0_i_)) and ((d_0_i_) < (len(s)))) and (((d_0_i_ % 2)) == (0))) or (((Result()[1])[d_0_i_]) == ((Result()[0])[(d_0_i_ // 2)]))))
    Ensures(Forall(int, lambda d_1_i_:
        not ((((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) and (((d_1_i_ % 2)) == (1))) or (((Result()[1])[d_1_i_]) == ((Result()[0])[((len(s)) - ((((d_1_i_) - (1)) // 2))) - (1)]))))
    # post-conditions-end

    # impl-start
    sorted : List[int] = BubbleSort(s)
    strange : List[int] = list(s)
    d_2_i_ : int = 0
    while (d_2_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(strange)))
        Invariant(Acc(list_pred(sorted)))
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_2_i_)) and ((d_2_i_) <= (len(s))))
        Invariant(len(sorted) == len(s))
        Invariant((len(strange)) == len(s))
        Invariant(Forall(int, lambda d_0_i_:
            Forall(int, lambda d_1_j_:
                Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len((sorted)))), ((sorted)[d_0_i_]) <= ((sorted)[d_1_j_])))))
        Invariant(Forall(int, lambda d_3_j_:
            (Implies((((0) <= (d_3_j_)) and ((d_3_j_) < (d_2_i_))) and (((d_3_j_ % 2)) == (0)), ((strange)[d_3_j_]) == ((sorted)[(d_3_j_ // 2)])), [[(strange)[d_3_j_]]])))
        Invariant(Forall(int, lambda d_4_j_:
            (Implies((((0) <= (d_4_j_)) and ((d_4_j_) < (d_2_i_))) and (((d_4_j_ % 2)) == (1)), ((strange)[d_4_j_]) == ((sorted)[((len(s)) - ((((d_4_j_) - (1)) // 2))) - (1)])), [[(strange)[d_4_j_]]])))
        # invariants-end
        if ((d_2_i_ % 2)) == (0):
            strange[d_2_i_] = (sorted)[(d_2_i_ // 2)]
        else:
            d_5_r_ : int = (((d_2_i_) - (1)) // 2)
            strange[d_2_i_] = (sorted)[((len(s)) - (d_5_r_)) - (1)]
        d_2_i_ = (d_2_i_) + (1)
    return (sorted, strange)
    # impl-end

def strange__sort__list(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(s)) == (len(Result())))
    # post-conditions-end

    # impl-start
    p : Tuple[List[int], List[int]] = strange__sort__list__helper(s)
    return p[1]
    # impl-end

def BubbleSort(a1 : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(a1)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a1)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(a1)) == (len(Result())))
    Ensures(Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len((Result())))), ((Result())[d_0_i_]) <= ((Result())[d_1_j_])))))
    # post-conditions-end

    # impl-start
    a : List[int] = list(a1)
    d_2_i_ : int = (len((a))) - (1)
    while (d_2_i_) > (0):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(Acc(list_pred(a1)))
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
        # invariants-end
        d_7_j_ : int = 0
        while (d_7_j_) < (d_2_i_):
            # invariants-start
            Invariant(Acc(list_pred(a)))
            Invariant(Acc(list_pred(a1)))
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
            # invariants-end
            if ((a)[d_7_j_]) > ((a)[(d_7_j_) + (1)]):
                rhs0_ : int = (a)[(d_7_j_) + (1)]
                (a)[(d_7_j_) + (1)] = (a)[d_7_j_]
                (a)[d_7_j_] = rhs0_
            d_7_j_ = (d_7_j_) + (1)
        d_2_i_ = (d_2_i_) - (1)
    return a
    # impl-end
