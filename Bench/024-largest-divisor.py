from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def largest__divisor(n : int) -> int:
    # pre-conditions-start
    Requires((n) > (1))
    # pre-conditions-end
    # post-conditions-start
    Ensures(((1) <= (Result())) and ((Result()) < (n)))
    Ensures(((n % Result())) == (0))
    Ensures(Forall(int, lambda d_0_k_:
        not (((Result()) < (d_0_k_)) and ((d_0_k_) < (n))) or (((n % d_0_k_)) != (0))))
    # post-conditions-end

    # impl-start
    d : int = (n) - (1)
    while (d) >= (1):
        # invariants-start
        Invariant(((1) <= (d)) and ((d) < (n)))
        Invariant(Forall(int, lambda d_1_k_:
            not (((d) < (d_1_k_)) and ((d_1_k_) < (n))) or (((n % d_1_k_)) != (0))))
        # invariants-end
        if ((n % d)) == (0):
            d = d
            return d
        d = (d) - (1)
    d = 1
    return d
    # impl-end