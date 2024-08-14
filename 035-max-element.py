from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def max__element(l : List[int]) -> int:
    Requires(Acc(list_pred(l)))
    Requires((len(l)) > (0))
    Ensures(Acc(list_pred(l)))
    Ensures(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(l)))) or (((l)[d_0_i_]) <= (Result()))))
    Ensures(Exists(int, lambda d_1_i_:
        (((d_1_i_) >= (0)) and ((d_1_i_) < (len(l)))) and (((l)[d_1_i_]) == (Result()))))
    result = int(0) # type : int
    result = (l)[0]
    d_2_i_ = int(0) # type : int
    d_2_i_ = 1
    while (d_2_i_) < (len(l)):
        Invariant(Acc(list_pred(l)))
        Invariant(((d_2_i_) >= (1)) and ((d_2_i_) <= (len(l))))
        Invariant(Forall(int, lambda d_3_i1_:
            not (((d_3_i1_) >= (0)) and ((d_3_i1_) < (d_2_i_))) or (((l)[d_3_i1_]) <= (result))))
        Invariant(Exists(int, lambda d_4_i1_:
            (((d_4_i1_) >= (0)) and ((d_4_i1_) < (d_2_i_))) and (((l)[d_4_i1_]) == (result))))
        if ((l)[d_2_i_]) > (result):
            result = (l)[d_2_i_]
        d_2_i_ = (d_2_i_) + (1)
    return result