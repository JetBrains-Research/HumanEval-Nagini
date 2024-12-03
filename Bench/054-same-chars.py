from typing import cast, List, Dict, Set, Optional, Union, FrozenSet
from nagini_contracts.contracts import *

def same_chars(s0: List[int], s1: List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s0)))
    Requires(Acc(list_pred(s1)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s0)))
    Ensures(Acc(list_pred(s1)))
    Ensures(Result() == (Forall(int, lambda i : Implies(((0 <= i) and (i < len(s0))), s0[i] in s1)) and 
                         Forall(int, lambda i : Implies(((0 <= i) and (i < len(s1))), s1[i] in s0))))
    # post-conditions-end

    # impl-start
    return (Forall(int, lambda i : Implies(((0 <= i) and (i < len(s0))), s0[i] in s1)) and 
            Forall(int, lambda i : Implies(((0 <= i) and (i < len(s1))), s1[i] in s0)))
    # impl-end
