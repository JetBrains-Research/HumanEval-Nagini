from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def Sum(a : List[int], s : int, t : int) -> int :
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    Requires(((0) <= (s)) and ((s) <= (t)) and ((t) <= (len(a))))
    # pre-conditions-end

    # impl-start
    if s == t:
        return 0
    else:
        return (a)[t - 1] + (Sum(a, s, t - 1))
    # impl-end

def minSubArraySum(a : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a)))
    Ensures(Forall(int, lambda d_1_p_:
        Forall(int, lambda d_2_q_:
            not ((((0) <= (d_1_p_)) and ((d_1_p_) <= (d_2_q_))) and ((d_2_q_) <= (len(a)))) or ((Sum(a, d_1_p_, d_2_q_)) >= (Result())))))
    Ensures(Exists(int, lambda d_3_k_:
        Exists(int, lambda d_4_m_:
            ((((0) <= (d_3_k_)) and ((d_3_k_) <= (d_4_m_))) and ((d_4_m_) <= (len(a)))) and ((Result()) == (Sum(a, d_3_k_, d_4_m_))))))
    # post-conditions-end

    # impl-start
    s : int = int(0)
    d_5_k_ : int = int(0)
    d_6_m_ : int = int(0)
    d_7_n_ : int = int(0)
    d_8_c_ : int = int(0)
    d_9_t_ : int = int(0)
    while (d_7_n_) < (len(a)):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(((0) <= (d_7_n_)) and ((d_7_n_) <= (len(a))))
        Invariant(Forall(int, lambda d_1_p_: (Implies(0 <= d_1_p_ and d_1_p_ < len(a), Sum(a, 0, d_1_p_ + 1) == Sum(a, 0, d_1_p_) + a[d_1_p_]))))
        Invariant(Forall(int, lambda st: 
            Implies(st >= 0 and st < len(a), 
                Forall(int, lambda d_1_p_: (Implies(st <= d_1_p_ and d_1_p_ < len(a), Sum(a, st, d_1_p_ + 1) == Sum(a, st, d_1_p_) + a[d_1_p_]))))))
        Invariant(((((0) <= (d_8_c_)) and ((d_8_c_) <= (d_7_n_))) and ((d_7_n_) <= (len(a)))))
        Invariant(((d_9_t_) == (Sum(a, d_8_c_, d_7_n_))))
        Invariant(((((0) <= (d_5_k_)) and ((d_5_k_) <= (d_6_m_))) and ((d_6_m_) <= (d_7_n_))))
        Invariant(((s) == (Sum(a, d_5_k_, d_6_m_))))
        Invariant(Forall(int, lambda d_10_b_:
            not (((0) <= (d_10_b_)) and ((d_10_b_) <= (d_7_n_))) or ((Sum(a, d_10_b_, d_7_n_)) >= (Sum(a, d_8_c_, d_7_n_)))))
        Invariant(Sum(a, d_8_c_, d_7_n_) >= Sum(a, d_5_k_, d_6_m_))
        Invariant(Forall(int, lambda d_11_p_:
            Forall(int, lambda d_12_q_:
                (not ((((0) <= (d_11_p_)) and ((d_11_p_) <= (d_12_q_))) and ((d_12_q_) <= (d_7_n_))) or ((Sum(a, d_11_p_, d_12_q_)) >= (Sum(a, d_5_k_, d_6_m_))), [[Sum(a, d_11_p_, d_12_q_)]]))))
        # invariants-end

        # assert-start
        Assert(Sum(a, d_8_c_, d_7_n_ + 1) == Sum(a, d_8_c_, d_7_n_) + a[d_7_n_]) 
        # assert-end
        d_9_t_ = (d_9_t_) + ((a)[d_7_n_])
        d_7_n_ = (d_7_n_) + (1)
        if (d_9_t_) > (0):
            d_8_c_ = d_7_n_
            d_9_t_ = 0
        elif (s) > (d_9_t_):
            d_5_k_ = d_8_c_
            d_6_m_ = d_7_n_
            s = d_9_t_
    return s
    # impl-end

