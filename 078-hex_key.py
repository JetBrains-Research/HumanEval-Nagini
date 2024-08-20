from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def IsPrimeHexDigit(c : int) -> bool :
    return ((((((c) == (2)) or ((c) == (3))) or ((c) == (5))) or ((c) == (7))) or ((c) == (11))) or ((c) == (13))

@Pure
def count__prime__hex__digits__rec(i : int, j : int, num : List[int]) -> int :
    Requires(Acc(list_pred(num)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(num))))
    if i == j:
        return 0
    else:
        return (1 if IsPrimeHexDigit(num[j - 1]) else 0) + count__prime__hex__digits__rec(i, j - 1, num)


def count__prime__hex__digits(s : List[int]) -> int:
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == (count__prime__hex__digits__rec(0, len(s), s)))
    Ensures(((0) <= (Result())) and ((Result()) <= (len(s))))
    count = int(0) # type : int
    count = 0
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (len(s)):
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(s))))
        Invariant((count) == (count__prime__hex__digits__rec(0, d_1_i_, s)))
        Invariant(count >= 0 and count <= d_1_i_)
        Invariant(Forall(int, lambda x : (Implies(x >= 0 and x < len(s), (count__prime__hex__digits__rec(0, x + 1, s)) == ((count__prime__hex__digits__rec(0, x, s) + ((1 if IsPrimeHexDigit((s)[x]) else 0))))), [[count__prime__hex__digits__rec(0, x + 1, s)]])))
        Assert((count__prime__hex__digits__rec(0, d_1_i_ + 1, s)) == ((count__prime__hex__digits__rec(0, d_1_i_, s) + ((1 if IsPrimeHexDigit((s)[d_1_i_]) else 0)))))
        count = (count) + ((1 if IsPrimeHexDigit((s)[d_1_i_]) else 0))
        d_1_i_ = (d_1_i_) + (1)
    return count