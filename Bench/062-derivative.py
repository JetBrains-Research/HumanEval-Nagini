from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def derivative(xs : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(xs)))
    Requires((len(xs)) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(xs)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == ((len(xs)) - (1)))
    Ensures(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(Result())))) or (((Result())[d_0_i_]) == (((xs)[(d_0_i_) + (1)]) * ((d_0_i_) + (1))))))
    # post-conditions-end

    # impl-start
    result = list([int(0)] * 0) # type : List[int]
    result = list([])
    d_1_i_ = int(0) # type : int
    d_1_i_ = 1
    while (d_1_i_) < (len(xs)):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(xs)))
        Invariant(((1) <= (d_1_i_)) and ((d_1_i_) <= (len(xs))))
        Invariant((len(result)) == ((d_1_i_) - (1)))
        Invariant(Forall(int, lambda d_2_j_:
            not (((0) <= (d_2_j_)) and ((d_2_j_) < (len(result)))) or (((result)[d_2_j_]) == (((xs)[(d_2_j_) + (1)]) * ((d_2_j_) + (1))))))
        # invariants-end
        result = (result) + [((xs)[d_1_i_]) * (d_1_i_)]
        d_1_i_ = (d_1_i_) + (1)
    return result
    # impl-end
