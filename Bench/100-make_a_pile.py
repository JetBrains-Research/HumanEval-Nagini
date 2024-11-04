from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def make__a__pile(n : int) -> List[int]:
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (n))
    Ensures(Forall(int, lambda d_0_i_:
        Implies(((1) <= (d_0_i_)) and ((d_0_i_) < (n)), ((Result())[d_0_i_]) == (((Result())[(d_0_i_) - (1)]) + (2)))))
    Ensures(Implies((n) > (0), ((Result())[0]) == (n)))
    # post-conditions-end

    # impl-start
    pile : List[int] = []
    if (n) == (0):
        return pile
    pile = [n]
    d_1_i_ : int = 1
    while (d_1_i_) < (n):
        # invariants-start
        Invariant(Acc(list_pred(pile)))
        Invariant(len(pile) == d_1_i_)
        Invariant(len(pile) > 0)
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (n)))
        Invariant((len(pile)) == (d_1_i_))
        Invariant(Forall(int, lambda d_2_j_:
            Implies(((1) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_)), ((pile)[d_2_j_]) == (((pile)[(d_2_j_) - (1)]) + (2)))))
        Invariant(Implies((n) > (0), ((pile)[0]) == (n)))
        # invariants-end
        pile = (pile) + [((pile)[(d_1_i_) - (1)]) + (2)]
        d_1_i_ = (d_1_i_) + (1)
    return pile
    # impl-end
