from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def modp__rec(n : int, p : int) -> int :
    # pure-pre-conditions-start
    Requires((p) > (0))
    Requires((n) >= (0))
    # pure-pre-conditions-end

    # pure-start
    if (n) == (0):
        return (1 % p)
    elif True:
        return ((modp__rec((n) - (1), p)) * (2)) % p
    # pure-end

def modp(n : int, p : int) -> int:
    # pre-conditions-start
    Requires((p) > (0))
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) == (modp__rec(n, p)))
    # post-conditions-end

    # impl-start
    r : int = (1 % p)
    i : int = 0
    while (i) < (n):
        # invariants-start
        Invariant(((0) <= (i)) and ((i) <= (n)))
        Invariant(Forall(int, lambda i: (Implies(i >= 0 and i < n, modp__rec(i + 1, p) == (modp__rec(i, p) * 2) % p))))
        Invariant((r) == (modp__rec(i, p)))
        # invariants-end
        # assert-start
        Assert(modp__rec(i + 1, p) == (modp__rec(i, p) * 2) % p)
        # assert-end
        r = (((r) * (2)) % p)
        i = (i) + (1)
    return r
    # impl-end
