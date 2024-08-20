from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def Prime(p : int) -> bool :
    return ((p) > (1)) and (Forall(int, lambda d_0_k_:
        not (((1) < (d_0_k_)) and ((d_0_k_) < (p))) or (((p % d_0_k_)) != (0))))

def is__prime(k : int) -> bool:
    Requires((k) >= (2))
    Ensures(not (Result()) or (Forall(int, lambda d_0_i_:
        not (((2) <= (d_0_i_)) and ((d_0_i_) < (k))) or ((k % d_0_i_) != (0)))))
    Ensures(not (not(Result())) or (Exists(int, lambda d_1_j_:
        (((2) <= (d_1_j_)) and ((d_1_j_) < (k))) and (((k % d_1_j_)) == (0)))))
    Ensures(Result() == Prime(k))
    result = False # type : bool
    d_2_i_ = int(0) # type : int
    d_2_i_ = 2
    result = True
    while (d_2_i_) < (k):
        Invariant(((2) <= (d_2_i_)) and ((d_2_i_) <= (k)))
        Invariant(not (not(result)) or (Exists(int, lambda d_3_j_:
            (((2) <= (d_3_j_)) and ((d_3_j_) < (d_2_i_))) and (((k % d_3_j_)) == (0)))))
        Invariant(not (result) or (Forall(int, lambda d_4_j_:
            not (((2) <= (d_4_j_)) and ((d_4_j_) < (d_2_i_))) or (((k % d_4_j_)) != (0)))))
        if ((k % d_2_i_)) == (0):
            result = False
        d_2_i_ = (d_2_i_) + (1)
    return result

def is__multiply__prime(x : int) -> bool:
    Requires((x) > (1))
    Ensures(Implies(Result(), Exists(int, lambda d_1_a_:
        Exists(int, lambda d_2_b_:
                (((Prime(d_1_a_)) and (Prime(d_2_b_)))) and ((x) == (((d_1_a_) * (d_2_b_))))))))
    Ensures(Implies(not(Result()), Forall(int, lambda d_10_i_:
        (Forall(int, lambda d_11_j_:
            (Implies((1 < d_10_i_ and 1 < d_11_j_ and (d_10_i_) < (x) and d_11_j_ < x), Implies((Prime(d_10_i_)), Implies((Prime(d_11_j_)), ((x) != (((d_10_i_) * (d_11_j_)))))))))))))
    d_4_a_ = int(2) # type : int
    result = False # type : bool
    while d_4_a_ < x:
        Invariant(x >= 2)
        Invariant(d_4_a_ >= 2 and d_4_a_ <= x) 
        Invariant(Implies(result, Exists(int, lambda d_1_a_:
            Exists(int, lambda d_2_b_:
                    (d_1_a_ < x and d_2_b_ < x and ((Prime(d_1_a_)) and (Prime(d_2_b_)))) and ((x) == (((d_1_a_) * (d_2_b_))))))))
        Invariant(Implies(not(result), Forall(int, lambda d_10_i_:
            (Forall(int, lambda d_11_j_:
                (Implies((1 < d_10_i_ and 1 < d_11_j_ and (d_10_i_) < (d_4_a_) and d_11_j_ < x), Implies((Prime(d_10_i_)), Implies((Prime(d_11_j_)), ((x) != (((d_10_i_) * (d_11_j_))))))), [[Prime(d_11_j_)]])), [[Prime(d_10_i_)]]))))
        if is__prime(d_4_a_):
            d_5_b_  = int(2) # type : int
            while d_5_b_ < x:
                Invariant(x >= 2)   
                Invariant(Prime(d_4_a_))
                Invariant(d_4_a_ >= 2 and d_4_a_ < x)
                Invariant(d_5_b_ >= 2 and d_5_b_ <= x)
                Invariant(Implies(result, Exists(int, lambda d_1_a_:
                    Exists(int, lambda d_2_b_:
                            (d_1_a_ < x and d_2_b_ < x and ((Prime(d_1_a_)) and (Prime(d_2_b_)))) and ((x) == (((d_1_a_) * (d_2_b_))))))))        
                Invariant(Implies(not(result), Forall(int, lambda d_8_j_:
                    (Implies(1 < d_8_j_ and d_8_j_ < d_5_b_, Implies(Prime(d_8_j_), ((x) != (((d_4_a_) * (d_8_j_)))))), [[Prime(d_8_j_)]]))))
                Invariant(Implies(not(result), Forall(int, lambda d_10_i_:
                    (Forall(int, lambda d_11_j_:
                        (Implies((1 < d_10_i_ and 1 < d_11_j_ and (d_10_i_) < (d_4_a_) and d_11_j_ < x), Implies((Prime(d_10_i_)), Implies((Prime(d_11_j_)), ((x) != (((d_10_i_) * (d_11_j_))))))), [[Prime(d_11_j_)]])), [[Prime(d_10_i_)]]))))
                if is__prime(d_5_b_) and x == d_4_a_ * d_5_b_:
                    result = True
                d_5_b_ = d_5_b_ + 1
        d_4_a_ = d_4_a_ + 1
    return result
