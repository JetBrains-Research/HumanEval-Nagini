from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def fib(n : int) -> int :
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() >= 0)
    # post-conditions-end

    # pure-start
    if (n) == (0):
        return 0
    elif (n) == (1):
        return 1
    elif True:
        return (fib((n) - (1))) + (fib((n) - (2)))
    # pure-end

def ComputeFib(n : int) -> int:
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) == (fib(n)))
    Ensures(Result() >= 0)
    # post-conditions-end

    # impl-start
    result : int = int(0)
    if (n) == (0):
        result = 0
        return result
    if (n) == (1):
        result = 1
        return result
    a : int = 0
    b : int = 1
    i : int = 2
    while (i) <= (n):
        # invariants-start
        Invariant(((2) <= (i)) and ((i) <= ((n) + (1))))
        Invariant((a) == (fib((i) - (2))))
        Invariant((b) == (fib((i) - (1))))
        # invariants-end
        temp : int = (a) + (b)
        a = b
        b = temp
        i = (i) + (1)
    result = b
    return result
    # impl-end
