from typing import List, Tuple
from nagini_contracts.contracts import *

@Pure 
def popcount(n : int) -> int :
    # pre-conditions-start
    Requires(n >= 0)
    # pre-conditions-end

    # impl-start
    if n == 0:
        return 0
    else:
        return ((n % 2)) + popcount(n // 10)
    # impl-end

def BubbleSort(a1 : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(a1), 1/2))
    Requires(Forall(int, lambda i : Implies(i >= 0 and i < len(a1), a1[i] >= 0)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a1), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(a1)) == (len(Result())))
    Ensures(Forall(int, lambda i : Implies(i >= 0 and i < len(Result()), Result()[i] >= 0)))
    Ensures(Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len((Result())))), popcount((Result())[d_0_i_]) <= popcount((Result())[d_1_j_])))))
    # post-conditions-end

    # impl-start
    a : List[int] = list(a1)
    d_2_i_ : int = (len((a))) - (1)
    while (d_2_i_) > (0):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(Forall(int, lambda i : Implies(i >= 0 and i < len(a), a[i] >= 0)))
        Invariant(Acc(list_pred(a1), 1/2))
        Invariant((len(a1)) == (len(a)))
        Invariant(not ((d_2_i_) < (0)) or ((len((a))) == (0)))
        Invariant(((-1) <= (d_2_i_)) and ((d_2_i_) < (len((a)))))
        Invariant(Forall(int, lambda d_3_ii_:
            (Forall(int, lambda d_4_jj_:
                (Implies((((d_2_i_) <= (d_3_ii_)) and ((d_3_ii_) < (d_4_jj_))) and ((d_4_jj_) < (len((a)))), popcount((a)[d_3_ii_]) <= popcount((a)[d_4_jj_])),
                    [[popcount((a)[d_4_jj_])]])),
                [[popcount((a)[d_3_ii_])]])))
        Invariant(Forall(int, lambda d_5_k_:
            (Forall(int, lambda d_6_k_k_:
                (Implies(((((0) <= (d_5_k_)) and ((d_5_k_) <= (d_2_i_))) and ((d_2_i_) < (d_6_k_k_)) and (d_6_k_k_) < (len((a)))), popcount((a)[d_5_k_]) <= popcount((a)[d_6_k_k_])),
                    [[popcount((a)[d_6_k_k_])]])),
                [[popcount((a)[d_5_k_])]])))
        # invariants-end
        d_7_j_ : int = 0
        while (d_7_j_) < (d_2_i_):
            # invariants-start
            Invariant(Acc(list_pred(a)))
            Invariant(Forall(int, lambda i : Implies(i >= 0 and i < len(a), a[i] >= 0)))
            Invariant(Acc(list_pred(a1), 1/2))
            Invariant((len(a1)) == (len(a)))
            Invariant((((0) < (d_2_i_)) and ((d_2_i_) < (len((a))))) and (((0) <= (d_7_j_)) and ((d_7_j_) <= (d_2_i_))))
            Invariant(Forall(int, lambda d_8_ii_:
                (Forall(int, lambda d_9_jj_:
                    (Implies((((d_2_i_) <= (d_8_ii_)) and ((d_8_ii_) <= (d_9_jj_))) and ((d_9_jj_) < (len((a)))), popcount((a)[d_8_ii_]) <= popcount((a)[d_9_jj_])),
                        [[popcount((a)[d_9_jj_])]])),
                    [[popcount((a)[d_8_ii_])]])))
            Invariant(Forall(int, lambda d_10_k_:
                (Forall(int, lambda d_11_k_k_:
                    (Implies(((((0) <= (d_10_k_)) and ((d_10_k_) <= (d_2_i_))) and ((d_2_i_) < (d_11_k_k_))) and ((d_11_k_k_) < (len((a)))), popcount((a)[d_10_k_]) <= popcount((a)[d_11_k_k_])),
                        [[popcount((a)[d_11_k_k_])]])),
                    [[popcount((a)[d_10_k_])]])))
            Invariant(Forall(int, lambda d_12_k_:
                (Implies(((0) <= (d_12_k_)) and ((d_12_k_) <= (d_7_j_)), popcount((a)[d_12_k_]) <= popcount((a)[d_7_j_])),
                    [[popcount((a)[d_12_k_])]])))
            # invariants-end
            if popcount((a)[d_7_j_]) > popcount((a)[(d_7_j_) + (1)]):
                rhs0_ : int = (a)[(d_7_j_) + (1)]
                (a)[(d_7_j_) + (1)] = (a)[d_7_j_]
                (a)[d_7_j_] = rhs0_
                # assert-start
                Assert(popcount((a)[d_7_j_]) <= popcount((a)[(d_7_j_) + (1)]))
                # assert-end
            d_7_j_ = (d_7_j_) + (1)
        d_2_i_ = (d_2_i_) - (1)
    return a
    # impl-end
