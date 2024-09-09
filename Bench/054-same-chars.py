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
    Ensures(Result() == (Forall(int, lambda d_0_i_ : Implies(((0 <= d_0_i_) and (d_0_i_ < len(s0))), s0[d_0_i_] in s1)) and 
                         Forall(int, lambda d_1_i_ : Implies(((0 <= d_1_i_) and (d_1_i_ < len(s1))), s1[d_1_i_] in s0))))
    # post-conditions-end

    # impl-start
    return (Forall(int, lambda d_0_i_ : Implies(((0 <= d_0_i_) and (d_0_i_ < len(s0))), s0[d_0_i_] in s1)) and 
            Forall(int, lambda d_1_i_ : Implies(((0 <= d_1_i_) and (d_1_i_ < len(s1))), s1[d_1_i_] in s0)))
    # impl-end