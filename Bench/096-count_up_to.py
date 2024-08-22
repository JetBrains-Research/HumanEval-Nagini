from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def IsPrime(n : int) -> bool :
    return ((n) > (1)) and (Forall(int, lambda d_0_k_:
        Implies(((2) <= (d_0_k_)) and ((d_0_k_) < (n)), ((n % d_0_k_)) != (0))))

def CountUpTo(n : int) -> List[int]:
    Requires((n) >= (0))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_2_i_:
        not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(Result())))) or (((Result())[d_2_i_]) < (n))))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(Result())))) or (IsPrime((Result())[d_1_i_]))))
    Ensures(Forall(int, lambda d_3_p_:
        Implies((((2) <= (d_3_p_)) and ((d_3_p_) < (n))) and IsPrime(d_3_p_),
            Exists(int, lambda x: x >= 0 and x < len(Result()) and Result()[x] == d_3_p_))))
    primes = list([int(0)] * 0) # type : List[int]
    primes = list([])
    if (n) <= (2):
        return primes
    d_4_i_ = int(0) # type : int
    d_4_i_ = 2
    while (d_4_i_) < (n):
        Invariant(Acc(list_pred(primes)))
        Invariant(((2) <= (d_4_i_)) and ((d_4_i_) <= (n)))
        Invariant(Forall(int, lambda x: 
            Implies(x >= 0 and x < len(primes), 2 <= primes[x] and primes[x] < n)))
        Invariant(Forall(int, lambda d_5_j_:
            (Implies(((0) <= (d_5_j_)) and ((d_5_j_) < (len(primes))), IsPrime((primes)[d_5_j_])), [[IsPrime((primes)[d_5_j_])]])))
        Invariant(Forall(int, lambda d_3_p_:
            Implies((((2) <= (d_3_p_)) and ((d_3_p_) < (d_4_i_))) and IsPrime(d_3_p_),
                Exists(int, lambda x: x >= 0 and x < len(primes) and primes[x] == d_3_p_))))
        if IsPrime(d_4_i_):
            primes = primes + [(d_4_i_)]
        d_4_i_ = (d_4_i_) + (1)
    return primes
