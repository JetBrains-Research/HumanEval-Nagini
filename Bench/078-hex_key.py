from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def IsPrimeHexDigit(c : int) -> bool :
    # pure-start
    return ((((((c) == (2)) or ((c) == (3))) or ((c) == (5))) or ((c) == (7))) or ((c) == (11))) or ((c) == (13))
    # pure-end

@Pure
def count__prime__hex__digits__rec(i : int, j : int, num : List[int]) -> int :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(num)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(num))))
    # pure-pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return (1 if IsPrimeHexDigit(num[j - 1]) else 0) + count__prime__hex__digits__rec(i, j - 1, num)
    # pure-end


def count__prime__hex__digits(s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == (count__prime__hex__digits__rec(0, len(s), s)))
    Ensures(((0) <= (Result())) and ((Result()) <= (len(s))))
    # post-conditions-end

    # impl-start
    count : int = 0
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant((count) == (count__prime__hex__digits__rec(0, i, s)))
        Invariant(count >= 0 and count <= i)
        Invariant(Forall(int, lambda x : (Implies(x >= 0 and x < len(s), (count__prime__hex__digits__rec(0, x + 1, s)) == ((count__prime__hex__digits__rec(0, x, s) + ((1 if IsPrimeHexDigit((s)[x]) else 0))))), [[count__prime__hex__digits__rec(0, x + 1, s)]])))
        # invariants-end
        
        # assert-start
        Assert((count__prime__hex__digits__rec(0, i + 1, s)) == ((count__prime__hex__digits__rec(0, i, s) + ((1 if IsPrimeHexDigit((s)[i]) else 0)))))
        # assert-end
        count = (count) + ((1 if IsPrimeHexDigit((s)[i]) else 0))
        i = (i) + (1)
    return count
    # impl-end
