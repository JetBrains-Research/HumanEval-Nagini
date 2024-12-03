from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def fib4__rec(n : int) -> int :
    # pre-conditions-start
    Requires(n >= 0)
    # pre-conditions-end

    # pure-start
    if (((n) == (0)) or ((n) == (1))) or ((n) == (2)):
        return 0
    elif (n) == (3):
        return 1
    elif True:
        return (((fib4__rec((n) - (1))) + (fib4__rec((n) - (2)))) + (fib4__rec((n) - (3)))) + (fib4__rec((n) - (4)))
    # pure-end

def fib4(n : int) -> int:
    # pre-conditions-start
    Requires(n >= 0)
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) == (fib4__rec(n)))
    # post-conditions-end

    # impl-start
    if (((n) == (0)) or ((n) == (1))) or ((n) == (2)):
        return 0
    if (n) == (3):
        return 1
    a : int = 0
    b : int = 0
    c : int = 0
    d : int = 1
    i : int = 4
    while (i) <= (n):
        # invariants-start
        Invariant(((4) <= (i)) and ((i) <= ((n) + (1))))
        Invariant((a) == (fib4__rec((i) - (4))))
        Invariant((b) == (fib4__rec((i) - (3))))
        Invariant((c) == (fib4__rec((i) - (2))))
        Invariant((d) == (fib4__rec((i) - (1))))
        # invariants-end
        temp : int = (((d) + (c)) + (b)) + (a)
        a = b
        b = c
        c = d
        d = temp
        i = (i) + (1)
    result : int = d
    return result
    # impl-end
