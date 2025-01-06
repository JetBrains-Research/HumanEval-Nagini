from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def largest__divisor(n : int) -> int:
    # pre-conditions-start
    Requires((n) > (1))
    # pre-conditions-end
    # post-conditions-start
    Ensures(((1) <= (Result())) and ((Result()) < (n)))
    Ensures(((n % Result())) == (0))
    Ensures(Forall(int, lambda k:
        not (((Result()) < (k)) and ((k) < (n))) or (((n % k)) != (0))))
    # post-conditions-end

    # impl-start
    d : int = (n) - (1)
    while (d) >= (1):
        # invariants-start
        Invariant(((1) <= (d)) and ((d) < (n)))
        Invariant(Forall(int, lambda k:
            not (((d) < (k)) and ((k) < (n))) or (((n % k)) != (0))))
        # invariants-end
        if ((n % d)) == (0):
            d = d
            return d
        d = (d) - (1)
    d = 1
    return d
    # impl-end
