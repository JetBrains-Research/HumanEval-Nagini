from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def largest__divisor(n : int) -> int:
    Requires((n) > (1))
    Ensures(((1) <= (Result())) and ((Result()) < (n)))
    Ensures(((n % Result())) == (0))
    Ensures(Forall(int, lambda d_0_k_:
        not (((Result()) < (d_0_k_)) and ((d_0_k_) < (n))) or (((n % d_0_k_)) != (0))))
    d = int(0) # type : int
    d = (n) - (1)
    while (d) >= (1):
        Invariant(((1) <= (d)) and ((d) < (n)))
        Invariant(Forall(int, lambda d_1_k_:
            not (((d) < (d_1_k_)) and ((d_1_k_) < (n))) or (((n % d_1_k_)) != (0))))
        if ((n % d)) == (0):
            d = d
            return d
        d = (d) - (1)
    d = 1
    return d