from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def fibfib(n : int) -> int :
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) >= (0))
    # post-conditions-end

    # pure-start
    if ((n) == (0)) or ((n) == (1)):
        return 0
    elif (n) == (2):
        return 1
    elif True:
        return ((fibfib((n) - (1))) + (fibfib((n) - (2)))) + (fibfib((n) - (3)))
    # pure-end

def ComputeFibFib(n : int) -> int:
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) >= (0))
    Ensures((Result()) == (fibfib(n)))
    # post-conditions-end

    # impl-start
    if ((n) == (0)) or ((n) == (1)):
        return 0
    if (n) == (2):
        return 1
    a : int = 0
    b : int = 0
    c : int = 1
    i : int = 3
    while (i) <= (n):
        # invariants-start
        Invariant(((3) <= (i)) and ((i) <= ((n) + (1))))
        Invariant((a) == (fibfib((i) - (3))))
        Invariant((b) == (fibfib((i) - (2))))
        Invariant((c) == (fibfib((i) - (1))))
        # invariants-end
        temp : int = ((c) + (b)) + (a)
        a = b
        b = c
        c = temp
        i = (i) + (1)
    result : int = c
    return result
    # impl-end
