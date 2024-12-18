from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def sort__array(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (len(s)))
    Ensures(not (((len(s)) > (0)) and ((((((s)[0]) + ((s)[(len(s)) - (1)])) % 2)) == (0))) or (Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            not ((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len(Result())))) or (((Result())[d_0_i_]) >= ((Result())[d_1_j_]))))))
    Ensures(not (((len(s)) > (0)) and ((((((s)[0]) + ((s)[(len(s)) - (1)])) % 2)) != (0))) or (Forall(int, lambda d_2_i_:
        Forall(int, lambda d_3_j_:
            not ((((0) <= (d_2_i_)) and ((d_2_i_) < (d_3_j_))) and ((d_3_j_) < (len(Result())))) or (((Result())[d_2_i_]) <= ((Result())[d_3_j_]))))))
    # post-conditions-end

    # impl-start
    sorted : List[int] = []
    if (len(s)) == (0):
        sorted = list([])
        return sorted
    elif (((((s)[0]) + ((s)[(len(s)) - (1)])) % 2)) == (0):
        # assert-start
        Assert(len(s) > 0)
        # assert-end
        d_4_t_ : List[int] = BubbleSort(s)
        # assert-start
        Assert(Forall(int, lambda d_0_i_:
            Forall(int, lambda d_1_j_:
                Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len((d_4_t_)))), ((d_4_t_)[d_0_i_]) <= ((d_4_t_)[d_1_j_])))))    
        # assert-end
        sorted = reverse(d_4_t_) 
        # assert-start
        Assert(Forall(int, lambda d_0_i_:
            Forall(int, lambda d_1_j_:
                Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len((sorted)))), ((sorted)[d_0_i_]) >= ((sorted)[d_1_j_])))))    
        Assert(((len(s)) > (0)) and ((((((s)[0]) + ((s)[(len(s)) - (1)])) % 2)) == (0)))
        # assert-end
        return sorted
    else:
        # assert-start
        Assert(len(s) > 0)
        # assert-end
        sorted = BubbleSort(s)
        # assert-start
        Assert(Forall(int, lambda d_0_i_:
            Forall(int, lambda d_1_j_:
                Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len((sorted)))), ((sorted)[d_0_i_]) <= ((sorted)[d_1_j_])))))    
        Assert(((len(s)) > (0)) and ((((((s)[0]) + ((s)[(len(s)) - (1)])) % 2)) != (0)))
        # assert-end
        return sorted
    # impl-end

def reverse(str : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(str), 1/2))
    Requires(Forall(int, lambda x: Forall(int, lambda y: not (((0) <= (x)) and ((x) < (y)) and ((y) < (len(str)))) or ((str)[x] <= (str)[y]))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(str), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda x: Forall(int, lambda y: not (((0) <= (x)) and ((x) < (y)) and ((y) < (len(Result())))) or ((Result())[x] >= (Result())[y]))))
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
        Invariant(Forall(int, lambda x: Forall(int, lambda y: not (((0) <= (x)) and ((x) < (y)) and ((y) < (len(str)))) or ((str)[x] <= (str)[y]))))
        Invariant(((d_12_i_) >= (0)) and ((d_12_i_) <= (len(str))))
        Invariant((len(rev)) == (d_12_i_))
        Invariant(Forall(int, lambda d_13_k_:
            not (((0) <= (d_13_k_)) and ((d_13_k_) < (d_12_i_))) or (((rev)[d_13_k_]) == ((str)[(len(str) - (1)) - (d_13_k_)]))))
        Invariant(Forall(int, lambda x: Forall(int, lambda y: (not (((0) <= (x)) and ((x) < (len(rev))) and (0 <= y and (y) < (len(str) - d_12_i_))) or ((str)[y] <= (rev)[x]), [[str[y] <= rev[x]]]))))
        Invariant(Forall(int, lambda x: Forall(int, lambda y: (not (((0) <= (x)) and ((x) < (y)) and ((y) < (len(rev)))) or ((rev)[x] >= (rev)[y]), [[rev[x] >= rev[y]]]))))
        # invariants-end
        rev = (rev) + [(str)[(len(str) - (d_12_i_)) - (1)]]
        d_12_i_ = (d_12_i_) + (1)
    return rev
    # impl-end

def BubbleSort(a1 : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(a1), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a1), 1/2))
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
        # invariants-end
        d_7_j_ : int = 0
        while (d_7_j_) < (d_2_i_):
            # invariants-start
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
            # invariants-end
            if ((a)[d_7_j_]) > ((a)[(d_7_j_) + (1)]):
                rhs0_ : int = (a)[(d_7_j_) + (1)]
                (a)[(d_7_j_) + (1)] = (a)[d_7_j_]
                (a)[d_7_j_] = rhs0_
            d_7_j_ = (d_7_j_) + (1)
        d_2_i_ = (d_2_i_) - (1)
    return a
    # impl-end
