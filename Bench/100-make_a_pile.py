from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def make__a__pile(n : int) -> List[int]:
    Requires((n) >= (0))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (n))
    Ensures(Forall(int, lambda d_0_i_:
        Implies(((1) <= (d_0_i_)) and ((d_0_i_) < (n)), ((Result())[d_0_i_]) == (((Result())[(d_0_i_) - (1)]) + (2)))))
    Ensures(Implies((n) > (0), ((Result())[0]) == (n)))
    pile = list([int(0)] * 0) # type : List[int]
    pile = list([])
    if (n) == (0):
        return pile
    pile = [n]
    d_1_i_ = int(0) # type : int
    d_1_i_ = 1
    while (d_1_i_) < (n):
        Invariant(Acc(list_pred(pile)))
        Invariant(len(pile) == d_1_i_)
        Invariant(len(pile) > 0)
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (n)))
        Invariant((len(pile)) == (d_1_i_))
        Invariant(Forall(int, lambda d_2_j_:
            Implies(((1) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_)), ((pile)[d_2_j_]) == (((pile)[(d_2_j_) - (1)]) + (2)))))
        Invariant(Implies((n) > (0), ((pile)[0]) == (n)))
        pile = (pile) + [((pile)[(d_1_i_) - (1)]) + (2)]
        d_1_i_ = (d_1_i_) + (1)
    return pile
