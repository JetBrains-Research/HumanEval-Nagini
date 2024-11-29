from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def modp__rec(n : int, p : int) -> int :
    # pre-conditions-start
    Requires((p) > (0))
    Requires((n) >= (0))
    # pre-conditions-end

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
    d_0_i_ : int = 0
    while (d_0_i_) < (n):
        # invariants-start
        Invariant(((0) <= (d_0_i_)) and ((d_0_i_) <= (n)))
        Invariant(Forall(int, lambda d_0_i_: (Implies(d_0_i_ >= 0 and d_0_i_ < n, modp__rec(d_0_i_ + 1, p) == (modp__rec(d_0_i_, p) * 2) % p))))
        Invariant((r) == (modp__rec(d_0_i_, p)))
        # invariants-end
        # assert-start
        Assert(modp__rec(d_0_i_ + 1, p) == (modp__rec(d_0_i_, p) * 2) % p)
        # assert-end
        r = (((r) * (2)) % p)
        d_0_i_ = (d_0_i_) + (1)
    return r
    # impl-end
