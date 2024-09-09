from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def InArray(a : List[int], x : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    # pre-conditions-end

    # impl-start
    return Exists(int, lambda d_0_i_:
        ((((0) <= (d_0_i_)) and ((d_0_i_) < (len((a)))) and ((a)[d_0_i_]) == (x))))
    # impl-end



def uniqueSorted(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len(s))), 
                ((s)[d_0_i_]) <= ((s)[d_1_j_])))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_9_k_:
        (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(Result()))), InArray(s, Result()[d_9_k_])))))
    Ensures(Forall(int, lambda d_2_i_:
        Forall(int, lambda d_3_j_:
            not ((((0) <= (d_2_i_)) and ((d_2_i_) < (d_3_j_))) and ((d_3_j_) < (len(Result())))) or (((Result())[d_2_i_]) < ((Result())[d_3_j_])))))
    # post-conditions-end

    # impl-start
    result = list([int(0)] * 0) # type : List[int]
    result = list([])
    d_6_i_ = int(0) # type : int
    d_6_i_ = 0
    while (d_6_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(s), 1/2))
        Invariant(Forall(int, lambda d_0_i_:
            Forall(int, lambda d_1_j_:
                Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len(s))), 
                    ((s)[d_0_i_]) <= ((s)[d_1_j_])))))
        Invariant(((0) <= (d_6_i_)) and ((d_6_i_) <= (len(s))))
        Invariant(Forall(int, lambda d_9_k_:
            (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(result))), InArray(s, result[d_9_k_])), [[InArray(s, result[d_9_k_])]])))
        Invariant(Implies(d_6_i_ < len(s), 
            Forall(int, lambda d_2_i_:
                (Implies(((0) <= (d_2_i_)) and ((d_2_i_) < (len(result))), result[d_2_i_] <= s[d_6_i_]), [[result[d_2_i_]]]))))
        Invariant(Forall(int, lambda d_7_k_:
            (Forall(int, lambda d_8_l_:
                (not ((((0) <= (d_7_k_)) and ((d_7_k_) < (d_8_l_))) and ((d_8_l_) < (len(result)))) or (((result)[d_7_k_]) < ((result)[d_8_l_])), 
                    [[(result)[d_8_l_]]])), 
                [[(result)[d_7_k_]]])))
        # invariants-end
        if ((len(result)) == (0)) or (((result)[(len(result)) - (1)]) != ((s)[d_6_i_])):
            # assert-start
            Assert(Implies(len(result) > 0, result[len(result) - 1] < s[d_6_i_]))
            Assert(Implies(len(result) > 0, 
                Forall(int, lambda d_11_j_:
                    Implies(0 <= d_11_j_ and d_11_j_ < len(result), result[d_11_j_] < s[d_6_i_]))))
            # assert-end
            result = (result) + [(s)[d_6_i_]]
        d_6_i_ = (d_6_i_) + (1)
    return result
    # impl-end

def unique(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_9_k_:
        (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(Result()))), InArray(s, Result()[d_9_k_])))))
    Ensures(Forall(int, lambda d_2_i_:
        Forall(int, lambda d_3_j_:
            not ((((0) <= (d_2_i_)) and ((d_2_i_) < (d_3_j_))) and ((d_3_j_) < (len(Result())))) or (((Result())[d_2_i_]) < ((Result())[d_3_j_])))))
    # post-conditions-end

    # impl-start
    a = BubbleSort(s)
    # assert-start
    Assert(Forall(int, lambda d_9_k_:
        (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(a))), InArray(s, a[d_9_k_])))))
    # assert-end
    b = uniqueSorted(a)
    # assert-start
    Assert(Forall(int, lambda d_9_k_:
        (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(a))), InArray(s, a[d_9_k_])))))
    Assert(Forall(int, lambda d_9_k_:
        (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(b))), InArray(a, b[d_9_k_])))))
    Assert(Forall(int, lambda d_9_k_:
        (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(b))), InArray(s, b[d_9_k_])))))
    # assert-end
    return b
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
    Ensures(Forall(int, lambda d_9_k_:
        (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(Result()))), InArray(a1, Result()[d_9_k_])))))
    # post-conditions-end

    # impl-start
    a : List[int] = []
    d_2_i_ = int(0) # type : int
    while d_2_i_ < len(a1):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(Acc(list_pred(a1), 1/2))
        Invariant(len(a) == d_2_i_)
        Invariant(0 <= d_2_i_ and d_2_i_ <= len(a1))
        Invariant(Forall(int, lambda d_9_k_:
            (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (d_2_i_)), a[d_9_k_] == a1[d_9_k_]))))
        Invariant(Forall(int, lambda d_9_k_:
            (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (d_2_i_)), InArray(a1, a[d_9_k_])), [[InArray(a1, a[d_9_k_])]])))
        Invariant(Forall(int, lambda d_9_k_:
            (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (d_2_i_)), InArray(a, a1[d_9_k_])), [[InArray(a, a1[d_9_k_])]])))
        # invariants-end
        a = a + [a1[d_2_i_]]
        # assert-start
        Assert(InArray(a1, a[d_2_i_]))
        # assert-end
        d_2_i_ = d_2_i_ + 1
    d_2_i_ = (len((a))) - (1)
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
        Invariant(Forall(int, lambda d_9_k_:
            (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(a))), InArray(a1, a[d_9_k_])), [[InArray(a1, a[d_9_k_])]])))
        # invariants-end
        d_7_j_ = int(0) # type : int
        d_7_j_ = 0
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
            Invariant(Forall(int, lambda d_9_k_:
                (Implies(((0) <= (d_9_k_)) and ((d_9_k_) < (len(a))), InArray(a1, a[d_9_k_])), [[InArray(a1, a[d_9_k_])]])))
            # invariants-end
            if ((a)[d_7_j_]) > ((a)[(d_7_j_) + (1)]):
                rhs0_ = (a)[(d_7_j_) + (1)] # type : int
                (a)[(d_7_j_) + (1)] = (a)[d_7_j_]
                (a)[d_7_j_] = rhs0_
            d_7_j_ = (d_7_j_) + (1)
        d_2_i_ = (d_2_i_) - (1)
    return a
    # impl-end
