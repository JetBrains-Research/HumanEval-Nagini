from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def upper__sum__rec(i : int, j : int, s : List[int]) -> int :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(s))))
    # pure-pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return s[j - 1] + upper__sum__rec(i, j - 1, s)
    # pure-end
    
def upper__sum(s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == (upper__sum__rec(0, len(s), s)))
    # post-conditions-end

    # impl-start
    res : int = 0
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant(Forall(int, lambda i: (Implies(((0) <= (i)) and ((i) < (len(s))), upper__sum__rec(0, i + 1, s) == upper__sum__rec(0, i, s) + s[i]), [[upper__sum__rec(0, i + 1, s)]])))
        Invariant((res) == (upper__sum__rec(0, i, s)))
        # invariants-end
        # assert-start
        Assert(upper__sum__rec(0, i + 1, s) == upper__sum__rec(0, i, s) + s[i])
        # assert-end
        res = (res) + (((s)[i]))
        i = (i) + (1)
    return res
    # impl-end

