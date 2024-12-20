from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def sum__chars__rec(i : int, j : int, lst : List[int]) -> int :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(lst)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(lst))))
    # pure-pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return ((lst)[j - 1] if (lst)[j - 1] < 100 else 0) + sum__chars__rec(i, j - 1, lst)
    # pure-end

def SumElementsWithAtMostTwoDigits(lst : List[int], k : int) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(lst)))
    Requires(1 <= k and k <= len(lst))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(lst)))
    Ensures(1 <= k and k <= len(lst))
    Ensures(Result() == sum__chars__rec(0, k, lst))
    # post-conditions-end

    # impl-start
    sum : int = 0
    i : int = 0
    while i < k:
        # invariants-start
        Invariant(Acc(list_pred(lst)))
        Invariant(1 <= k and k <= len(lst))
        Invariant(((0) <= (i)) and ((i) <= (len(lst))) and i <= k)
        Invariant(Forall(int, lambda i : (Implies(i >= 0 and i < k, sum__chars__rec(0, i + 1, lst) == sum__chars__rec(0, i, lst) + ((lst)[i] if (lst)[i] < 100 else 0)), [[sum__chars__rec(0, i + 1, lst)]])))
        Invariant((sum) == (sum__chars__rec(0, i, lst)))
        # invariants-end
        # assert-start
        Assert(sum__chars__rec(0, i + 1, lst) == sum__chars__rec(0, i, lst) + ((lst)[i] if (lst)[i] < 100 else 0))
        # assert-end
        if (lst)[i] < 100:
            sum = (sum) + ((lst)[i])
        i = (i) + (1)
    return sum
    # impl-end
