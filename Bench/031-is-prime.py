from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def is__prime(k : int) -> bool:
    Requires((k) >= (2))
    Ensures(not (Result()) or (Forall(int, lambda d_0_i_:
        not (((2) <= (d_0_i_)) and ((d_0_i_) < (k))) or ((k % d_0_i_) != (0)))))
    Ensures(not (not(Result())) or (Exists(int, lambda d_1_j_:
        (((2) <= (d_1_j_)) and ((d_1_j_) < (k))) and (((k % d_1_j_)) == (0)))))
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