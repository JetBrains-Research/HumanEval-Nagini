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
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or (((Result())[i]) == (((xs)[(i) + (1)]) * ((i) + (1))))))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    i : int = 1
    while (i) < (len(xs)):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(xs)))
        Invariant(((1) <= (i)) and ((i) <= (len(xs))))
        Invariant((len(result)) == ((i) - (1)))
        Invariant(Forall(int, lambda j:
            not (((0) <= (j)) and ((j) < (len(result)))) or (((result)[j]) == (((xs)[(j) + (1)]) * ((j) + (1))))))
        # invariants-end
        result = (result) + [((xs)[i]) * (i)]
        i = (i) + (1)
    return result
    # impl-end
