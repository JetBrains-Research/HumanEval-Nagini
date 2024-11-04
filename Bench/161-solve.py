from typing import List
from nagini_contracts.contracts import *

def solve(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result()), 1/2))
    Ensures(Acc(list_pred(s), 1/2))
    Ensures((len(s)) == (len(Result())))
    Ensures(Implies(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(s)))) or (not(is__alpha((s)[d_0_i_])))), Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) or (((s)[d_1_i_]) == ((Result())[((len(Result())) - (1)) - (d_1_i_)])))))
    Ensures(Implies(Exists(int, lambda d_2_i_:
        (((0) <= (d_2_i_)) and ((d_2_i_) < (len(s)))) and (is__alpha((s)[d_2_i_]))), Forall(int, lambda d_3_i_:
        not (((0) <= (d_3_i_)) and ((d_3_i_) < (len(Result())))) or ((((Result())[d_3_i_]) == (flip__case((s)[d_3_i_])) if is__alpha((s)[d_3_i_]) else ((Result())[d_3_i_]) == ((s)[d_3_i_]))))))
    # post-conditions-end

    # impl-start
    t : List[int] = []
    d_4_flag_ : bool = False
    d_5_i_ : int = 0
    while (d_5_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(t)))
        Invariant(Acc(list_pred(s), 1/2))
        Invariant(((0) <= (d_5_i_)) and ((d_5_i_) <= (len(s))))
        Invariant((len(t)) == (d_5_i_))
        Invariant(Implies(d_4_flag_, Exists(int, lambda d_6_j_:
            (((0) <= (d_6_j_)) and ((d_6_j_) < (d_5_i_))) and (is__alpha((s)[d_6_j_])))))
        Invariant(Implies(Exists(int, lambda d_6_j_:
            (((0) <= (d_6_j_)) and ((d_6_j_) < (d_5_i_))) and (is__alpha((s)[d_6_j_]))), d_4_flag_))
        Invariant(Implies(not(d_4_flag_), Forall(int, lambda d_7_j_:
            Implies(((0) <= (d_7_j_)) and (d_7_j_) < (d_5_i_), not(is__alpha((s)[d_7_j_]))))))
        Invariant(Implies(Forall(int, lambda d_7_j_:
            Implies(((0) <= (d_7_j_)) and (d_7_j_) < (d_5_i_), not(is__alpha((s)[d_7_j_])))), not(d_4_flag_)))
        Invariant(Forall(int, lambda d_7_j_:
            (Implies(((0) <= (d_7_j_)) and ((d_7_j_) < (d_5_i_)), ((t)[d_7_j_]) == ((flip__case((s)[d_7_j_]) if is__alpha((s)[d_7_j_]) else (s)[d_7_j_]))), [[]])))
        # invariants-end
        if is__alpha((s)[d_5_i_]):
            t = (t) + [flip__case((s)[d_5_i_])]
            d_4_flag_ = True
        else:
            t = (t) + [(s)[d_5_i_]]
        d_5_i_ = (d_5_i_) + (1)
    if not(d_4_flag_):
        t = reverse(t)
    return t
    # impl-end

def reverse(str : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(str), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(str), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(str == Old(str))
    Ensures((len(Result())) == (len(str)))
    Ensures(Forall(int, lambda d_11_k_:
        not (((0) <= (d_11_k_)) and ((d_11_k_) < (len(str)))) or (((Result())[d_11_k_]) == ((str)[((len(str)) - (1)) - (d_11_k_)]))))
    # post-conditions-end

    # impl-start
    rev : List[int] = []
    d_12_i_ : int = 0
    while (d_12_i_) < (len(str)):
        # invariants-start
        Invariant(Acc(list_pred(str), 1/2))
        Invariant(Acc(list_pred(rev)))
        Invariant(((d_12_i_) >= (0)) and ((d_12_i_) <= (len(str))))
        Invariant((len(rev)) == (d_12_i_))
        Invariant(Forall(int, lambda d_13_k_:
            not (((0) <= (d_13_k_)) and ((d_13_k_) < (d_12_i_))) or (((rev)[d_13_k_]) == ((str)[(len(str) - (1)) - (d_13_k_)]))))
        # invariants-end
        rev = (rev) + [(str)[(len(str) - (d_12_i_)) - (1)]]
        d_12_i_ = (d_12_i_) + (1)
    return rev
    # impl-end

@Pure
def is__alpha(c : int) -> bool :
    # impl-start
    return (((97) <= (c)) and ((c) <= (122))) or (((65) <= (c)) and ((c) <= (90)))
    # impl-end 

@Pure
def flip__case(c : int) -> int :
    # impl-start
    if ((97) <= (c)) and ((c) <= (122)):
        return ((c) - (97)) + (65)
    elif True:
        return ((c) - (65)) + (97)
    # impl-end
