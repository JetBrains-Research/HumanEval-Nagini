from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def is__prime(s : str) -> bool:
    # pre-conditions-start
    Requires((len(s)) >= (2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(not (Result()) or (Forall(int, lambda d_0_i_:
        not (((2) <= (d_0_i_)) and ((d_0_i_) < (len(s)))) or ((len(s) % d_0_i_) != (0)))))
    Ensures(not (not(Result())) or (Exists(int, lambda d_1_j_:
        (((2) <= (d_1_j_)) and ((d_1_j_) < (len(s)))) and (((len(s) % d_1_j_)) == (0)))))
    # post-conditions-end

    # impl-start
    d_2_i_ : int = 2
    result : bool = True
    while (d_2_i_) < (len(s)):
        # invariants-start
        Invariant(((2) <= (d_2_i_)) and ((d_2_i_) <= (len(s))))
        Invariant(not (not(result)) or (Exists(int, lambda d_3_j_:
            (((2) <= (d_3_j_)) and ((d_3_j_) < (d_2_i_))) and (((len(s) % d_3_j_)) == (0)))))
        Invariant(not (result) or (Forall(int, lambda d_4_j_:
            not (((2) <= (d_4_j_)) and ((d_4_j_) < (d_2_i_))) or (((len(s) % d_4_j_)) != (0)))))
        # invariants-end
        if ((len(s) % d_2_i_)) == (0):
            result = False
        d_2_i_ = (d_2_i_) + (1)
    return result
    # impl-end
