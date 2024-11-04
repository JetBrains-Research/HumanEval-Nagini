from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

    # impl-start
    if i == j:
        return 0
    else:
        return (s)[j - 1] + (psum(i, j - 1, s))
    # impl-end

def below__zero(ops : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(ops)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(ops)))
    Ensures(not (Result()) or (Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) <= (len(ops)))) or ((psum(0, d_1_i_, ops)) >= (0)))))
    Ensures(not (not(Result())) or (Exists(int, lambda d_2_i_:
        (((0) <= (d_2_i_)) and ((d_2_i_) <= (len(ops)))) and ((psum(0, d_2_i_, ops)) < (0)))))
    # post-conditions-end

    # impl-start
    d_3_balance_ : int = 0
    d_4_i_ : int = 0
    
    while (d_4_i_) < (len(ops)):
        # invariants-start
        Invariant(Acc(list_pred(ops)))
        Invariant(((0) <= (d_4_i_)) and ((d_4_i_) <= (len(ops))))
        Invariant((d_3_balance_) == (psum(0, d_4_i_, ops)))
        Invariant(Forall(int, lambda d_2_i_: (not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(ops)))) or ((psum(0, d_2_i_ + 1, ops)) == (psum(0, d_2_i_, ops) + ops[d_2_i_])), [[psum(0, d_2_i_ + 1, ops)]])))
        Invariant(Forall(int, lambda d_5_j_:
            (not (((0) <= (d_5_j_)) and ((d_5_j_) <= (d_4_i_))) or ((psum(0, d_5_j_, ops)) >= (0)), [[psum(0, d_5_j_, ops)]])))
        # invariants-end

        # assert-start
        Assert((psum(0, (d_4_i_) + (1), ops)) == ((psum(0, d_4_i_, ops)) + ((ops)[d_4_i_])))
        # assert-end
        
        d_3_balance_ = (d_3_balance_) + ((ops)[d_4_i_])
        if (d_3_balance_) < (0):
            return False
        d_4_i_ = (d_4_i_) + (1)

    return True
    # impl-end