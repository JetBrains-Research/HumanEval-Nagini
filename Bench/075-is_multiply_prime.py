from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def Prime(p : int) -> bool :
    # impl-start
    return ((p) > (1)) and (Forall(int, lambda d_0_k_:
        not (((1) < (d_0_k_)) and ((d_0_k_) < (p))) or (((p % d_0_k_)) != (0))))
    # impl-end

def is__prime(k : int) -> bool:
    # pre-conditions-start
    Requires((k) >= (2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(not (Result()) or (Forall(int, lambda d_0_i_:
        not (((2) <= (d_0_i_)) and ((d_0_i_) < (k))) or ((k % d_0_i_) != (0)))))
    Ensures(not (not(Result())) or (Exists(int, lambda d_1_j_:
        (((2) <= (d_1_j_)) and ((d_1_j_) < (k))) and (((k % d_1_j_)) == (0)))))
    Ensures(Result() == Prime(k))
    # post-conditions-end

    # impl-start
    result = False # type : bool
    d_2_i_ = int(0) # type : int
    d_2_i_ = 2
    result = True
    while (d_2_i_) < (k):
        # invariants-start
        Invariant(((2) <= (d_2_i_)) and ((d_2_i_) <= (k)))
        Invariant(not (not(result)) or (Exists(int, lambda d_3_j_:
            (((2) <= (d_3_j_)) and ((d_3_j_) < (d_2_i_))) and (((k % d_3_j_)) == (0)))))
        Invariant(not (result) or (Forall(int, lambda d_4_j_:
            not (((2) <= (d_4_j_)) and ((d_4_j_) < (d_2_i_))) or (((k % d_4_j_)) != (0)))))
        # invariants-end
        if ((k % d_2_i_)) == (0):
            result = False
        d_2_i_ = (d_2_i_) + (1)
    return result
    # impl-end

def is__multiply__prime(x : int) -> bool:
    # pre-conditions-start
    Requires((x) > (1))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Implies(Result(), Exists(int, lambda d_1_a_:
        d_1_a_< x and 
        ((Prime(d_1_a_)) and 
        Exists(int, lambda d_2_b_:
            d_2_b_ < x and 
            (Prime(d_2_b_)) and
            Exists(int, lambda d_3_c_:
                (d_3_c_ < x) and (Prime(d_3_c_)) and ((x) == (((d_1_a_) * (d_2_b_)) * (d_3_c_)))))))))
    Ensures(Implies(not(Result()), Forall(int, lambda d_10_i_:
        (Implies(1 < d_10_i_ and d_10_i_ < x, 
            Forall(int, lambda d_11_j_:
                (Implies((1 < d_11_j_ and d_11_j_ < x), 
                    (Forall(int, lambda d_12_k_:
                        (Implies(1 < d_12_k_ and d_12_k_ < x, 
                            Implies((Prime(d_10_i_)), Implies((Prime(d_11_j_)), Implies(Prime(d_12_k_), ((x) != (((d_10_i_) * (d_11_j_) * (d_12_k_)))))))))))))))))))
    # post-conditions-end

    # impl-start
    d_4_a_ = int(2) # type : int
    result = False # type : bool
    while d_4_a_ < x:
        # invariants-start
        Invariant(x >= 2)
        Invariant(d_4_a_ >= 2 and d_4_a_ <= x) 
        Invariant(Implies(result, Exists(int, lambda d_1_a_:
            d_1_a_< x and 
            ((Prime(d_1_a_)) and 
            Exists(int, lambda d_2_b_:
                d_2_b_ < x and 
                (Prime(d_2_b_)) and
                Exists(int, lambda d_3_c_:
                    (d_3_c_ < x) and (Prime(d_3_c_)) and ((x) == (((d_1_a_) * (d_2_b_)) * (d_3_c_)))))))))
        Invariant(Implies(not(result), Forall(int, lambda d_10_i_:
            (Implies(1 < d_10_i_ and d_10_i_ < d_4_a_, 
                Forall(int, lambda d_11_j_:
                    (Implies((1 < d_11_j_ and d_11_j_ < x), 
                        (Forall(int, lambda d_12_k_:
                            (Implies(1 < d_12_k_ and d_12_k_ < x, 
                                Implies((Prime(d_10_i_)), Implies((Prime(d_11_j_)), Implies(Prime(d_12_k_), ((x) != (((d_10_i_) * (d_11_j_) * (d_12_k_)))))))), 
                                    [[Prime(d_12_k_)]])))), 
                        [[Prime(d_11_j_)]]))), 
                [[Prime(d_10_i_)]]))))
        # invariants-end
        if is__prime(d_4_a_):
            d_5_b_  = int(2) # type : int
            while d_5_b_ < x:
                # invariants-start
                Invariant(x >= 2)   
                Invariant(Prime(d_4_a_))
                Invariant(d_4_a_ >= 2 and d_4_a_ < x)
                Invariant(d_5_b_ >= 2 and d_5_b_ <= x)
                Invariant(Implies(result, Exists(int, lambda d_1_a_:
                    d_1_a_< x and 
                    ((Prime(d_1_a_)) and 
                    Exists(int, lambda d_2_b_:
                        d_2_b_ < x and 
                        (Prime(d_2_b_)) and
                        Exists(int, lambda d_3_c_:
                            (d_3_c_ < x) and (Prime(d_3_c_)) and ((x) == (((d_1_a_) * (d_2_b_)) * (d_3_c_)))))))))
                Invariant(Implies(not(result), Forall(int, lambda d_10_i_:
                    (Implies(1 < d_10_i_ and d_10_i_ < d_4_a_, 
                        Forall(int, lambda d_11_j_:
                            (Implies((1 < d_11_j_ and d_11_j_ < x), 
                                (Forall(int, lambda d_12_k_:
                                    (Implies(1 < d_12_k_ and d_12_k_ < x, 
                                        Implies((Prime(d_10_i_)), Implies((Prime(d_11_j_)), Implies(Prime(d_12_k_), ((x) != (((d_10_i_) * (d_11_j_) * (d_12_k_)))))))), 
                                            [[Prime(d_12_k_)]])))), 
                                [[Prime(d_11_j_)]]))), 
                        [[Prime(d_10_i_)]]))))
                Invariant(Implies(not(result), 
                    Forall(int, lambda d_11_j_:
                        (Implies((1 < d_11_j_ and d_11_j_ < d_5_b_), 
                            (Forall(int, lambda d_12_k_:
                                (Implies(1 < d_12_k_ and d_12_k_ < x, 
                                        Implies((Prime(d_11_j_)), Implies(Prime(d_12_k_), (x) != (((d_4_a_) * (d_11_j_) * (d_12_k_)))))), 
                                [[Prime(d_12_k_)]])))), 
                        [[Prime(d_11_j_)]]))))
                # invariants-end
                if is__prime(d_5_b_):
                    d_6_c_ = int(2) # type : int
                    while d_6_c_ < x:
                        # invariants-start
                        Invariant(x >= 2)
                        Invariant(Prime(d_4_a_))
                        Invariant(Prime(d_5_b_))
                        Invariant(d_4_a_ >= 2 and d_4_a_ < x)
                        Invariant(d_5_b_ >= 2 and d_5_b_ < x)
                        Invariant(d_6_c_ >= 2 and d_6_c_ <= x)
                        Invariant(Implies(result, Exists(int, lambda d_1_a_:
                            d_1_a_< x and 
                            ((Prime(d_1_a_)) and 
                            Exists(int, lambda d_2_b_:
                                d_2_b_ < x and 
                                (Prime(d_2_b_)) and
                                Exists(int, lambda d_3_c_:
                                    (d_3_c_ < x) and (Prime(d_3_c_)) and ((x) == (((d_1_a_) * (d_2_b_)) * (d_3_c_)))))))))
                        Invariant(Implies(not(result), Forall(int, lambda d_10_i_:
                            (Implies(1 < d_10_i_ and d_10_i_ < d_4_a_, 
                                Forall(int, lambda d_11_j_:
                                    (Implies((1 < d_11_j_ and d_11_j_ < x), 
                                        (Forall(int, lambda d_12_k_:
                                            (Implies(1 < d_12_k_ and d_12_k_ < x, 
                                                Implies((Prime(d_10_i_)), Implies((Prime(d_11_j_)), Implies(Prime(d_12_k_), ((x) != (((d_10_i_) * (d_11_j_) * (d_12_k_)))))))), 
                                                    [[Prime(d_12_k_)]])))), 
                                        [[Prime(d_11_j_)]]))), 
                                [[Prime(d_10_i_)]]))))
                        Invariant(Implies(not(result), 
                            Forall(int, lambda d_11_j_:
                                (Implies((1 < d_11_j_ and d_11_j_ < d_5_b_), 
                                    (Forall(int, lambda d_12_k_:
                                        (Implies(1 < d_12_k_ and d_12_k_ < x, 
                                                Implies((Prime(d_11_j_)), Implies(Prime(d_12_k_), (x) != (((d_4_a_) * (d_11_j_) * (d_12_k_)))))), 
                                        [[Prime(d_12_k_)]])))), 
                                [[Prime(d_11_j_)]]))))
                        Invariant(Implies(not(result), 
                            Forall(int, lambda d_12_k_: 
                                (Implies(1 < d_12_k_ and d_12_k_ < d_6_c_, 
                                    Implies((Prime(d_12_k_)), ((x) != (((d_4_a_) * (d_5_b_) * (d_12_k_)))))), 
                                [[Prime(d_12_k_)]]))))
                        # invariants-end
                        if (is__prime(d_6_c_)) and ((x) == (((d_4_a_) * (d_5_b_)) * (d_6_c_))):
                            result = True
                        d_6_c_ = d_6_c_ + 1
                d_5_b_ = d_5_b_ + 1
        d_4_a_ = d_4_a_ + 1
    return result
    # impl-end
