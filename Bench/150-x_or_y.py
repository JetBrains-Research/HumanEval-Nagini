from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def IsPrime(n : int) -> bool :
    # pure-start
    return ((n) > (1)) and (Forall(int, lambda k:
        not (((2) <= (k)) and ((k) < (n))) or (((n % k)) != (0))))
    # pure-end


def x__or__y(n : int, x : int, y : int) -> int:
    # pre-conditions-start
    Requires(n > 1)
    # pre-conditions-end
    # post-conditions-start
    Ensures(not (IsPrime(n)) or ((Result()) == (x)))
    Ensures(not (not(IsPrime(n))) or ((Result()) == (y)))
    # post-conditions-end

    # impl-start
    i = 2
    while i < n:
        # invariants-start
        Invariant(2 <= i and i <= n)
        Invariant(Forall(int, lambda k: not (2 <= k and k < i) or (n % k != 0)))
        # invariants-end
        if n % i == 0:
            return y
        i += 1
    return x
    # impl-end
