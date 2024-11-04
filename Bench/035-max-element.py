from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def max__element(l : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(l)))
    Requires((len(l)) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(l)))
    Ensures(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(l)))) or (((l)[d_0_i_]) <= (Result()))))
    Ensures(Exists(int, lambda d_1_i_:
        (((d_1_i_) >= (0)) and ((d_1_i_) < (len(l)))) and (((l)[d_1_i_]) == (Result()))))
    # post-conditions-end

    # impl-start
    result : int = (l)[0]
    d_2_i_ : int = 1
    while (d_2_i_) < (len(l)):
        # invariants-start
        Invariant(Acc(list_pred(l)))
        Invariant(((d_2_i_) >= (1)) and ((d_2_i_) <= (len(l))))
        Invariant(Forall(int, lambda d_3_i1_:
            not (((d_3_i1_) >= (0)) and ((d_3_i1_) < (d_2_i_))) or (((l)[d_3_i1_]) <= (result))))
        Invariant(Exists(int, lambda d_4_i1_:
            (((d_4_i1_) >= (0)) and ((d_4_i1_) < (d_2_i_))) and (((l)[d_4_i1_]) == (result))))
        # invariants-end
        if ((l)[d_2_i_]) > (result):
            result = (l)[d_2_i_]
        d_2_i_ = (d_2_i_) + (1)
    return result
    # impl-end
