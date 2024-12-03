from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def make__a__pile(n : int) -> List[int]:
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (n))
    Ensures(Forall(int, lambda i:
        Implies(((1) <= (i)) and ((i) < (n)), ((Result())[i]) == (((Result())[(i) - (1)]) + (2)))))
    Ensures(Implies((n) > (0), ((Result())[0]) == (n)))
    # post-conditions-end

    # impl-start
    pile : List[int] = []
    if (n) == (0):
        return pile
    pile = [n]
    i : int = 1
    while (i) < (n):
        # invariants-start
        Invariant(Acc(list_pred(pile)))
        Invariant(len(pile) == i)
        Invariant(len(pile) > 0)
        Invariant(((0) <= (i)) and ((i) <= (n)))
        Invariant((len(pile)) == (i))
        Invariant(Forall(int, lambda j:
            Implies(((1) <= (j)) and ((j) < (i)), ((pile)[j]) == (((pile)[(j) - (1)]) + (2)))))
        Invariant(Implies((n) > (0), ((pile)[0]) == (n)))
        # invariants-end
        pile = (pile) + [((pile)[(i) - (1)]) + (2)]
        i = (i) + (1)
    return pile
    # impl-end
