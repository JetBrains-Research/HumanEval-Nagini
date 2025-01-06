from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def ThreeDistinct(s : List[int], i : int) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(((0) < (i)) and ((i) < ((len(s)) - (1))))
    # pure-pre-conditions-end

    # pure-start
    return ((((s)[(i) - (1)]) != ((s)[i])) and (((s)[i]) != ((s)[(i) + (1)]))) and (((s)[(i) - (1)]) != ((s)[(i) + (1)]))
    # pure-end

@Pure
def Happy(s : List[int]) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pure-pre-conditions-end

    # pure-start
    return ((len(s)) >= (3)) and (Forall(int, lambda i:
        Implies(((0) < (i)) and ((i) < ((len(s)) - (1))), ThreeDistinct(s, i))))
    # pure-end

def IsHappy(s : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == (Happy(s)))
    # post-conditions-end

    # impl-start
    if (len(s)) < (3):
        return False
    i : int = 1
    while (i) < ((len(s)) - (1)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) < (i)) and ((i) <= ((len(s)) - (1))))
        Invariant(len(s) >= 3)
        Invariant(Forall(int, lambda j:
            Implies(((0) < (j)) and ((j) < (i)), ThreeDistinct(s, j))))
        # invariants-end
        if not(ThreeDistinct(s, i)):
            return False
        i = (i) + (1)
    return True
    # impl-end
