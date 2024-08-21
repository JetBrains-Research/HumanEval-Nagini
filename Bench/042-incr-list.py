from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def incr__list(l : List[int]) -> List[int]:
    Requires(Acc(list_pred(l)))
    Ensures(Acc(list_pred(l)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (len(l)))
    Ensures(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(l)))) or (((Result())[d_0_i_]) == (((l)[d_0_i_]) + (1)))))
    result = list([int(0)] * 0) # type : List[int]
    result = list([])
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (len(l)):
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(l)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(l))))
        Invariant((len(result)) == (d_1_i_))
        Invariant(Forall(int, lambda d_2_i1_:
            not (((0) <= (d_2_i1_)) and ((d_2_i1_) < (d_1_i_))) or (((result)[d_2_i1_]) == (((l)[d_2_i1_]) + (1)))))
        result = (result) + ([((l)[d_1_i_]) + (1)])
        d_1_i_ = (d_1_i_) + (1)
    return result
