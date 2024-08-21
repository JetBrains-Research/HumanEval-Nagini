from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def Compare(scores : List[int], guesses : List[int]) -> List[int]:
    Requires(Acc(list_pred(guesses)))
    Requires(Acc(list_pred(scores)))
    Requires((len((scores))) == (len((guesses))))
    Ensures(Acc(list_pred(guesses)))
    Ensures(Acc(list_pred(scores)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len((Result()))) == (len((scores))))
    Ensures((len((scores))) == (len((guesses))))
    Ensures(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len((Result()))))) or (((Result())[d_0_i_]) == (abs(((scores)[d_0_i_]) - ((guesses)[d_0_i_]))))))
    result = [int(0)] * 0 # type : List[int]
    nw0_ = [int(0)] * len((scores)) # type : List[int]
    result = nw0_
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (len((scores))):
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(guesses)))
        Invariant(Acc(list_pred(scores)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len((scores)))))
        Invariant((len((result))) == (len((scores))))
        Invariant((len((scores))) == (len((guesses))))
        Invariant(Forall(int, lambda d_2_k_:
            not (((0) <= (d_2_k_)) and ((d_2_k_) < (d_1_i_))) or (((result)[d_2_k_]) == (abs(((scores)[d_2_k_]) - ((guesses)[d_2_k_]))))))
        (result)[(d_1_i_)] = abs(((scores)[d_1_i_]) - ((guesses)[d_1_i_]))
        d_1_i_ = (d_1_i_) + (1)
    return result

@Pure
def abs(x : int) -> int :
    if (x) < (0):
        return (0) - (x)
    elif True:
        return x