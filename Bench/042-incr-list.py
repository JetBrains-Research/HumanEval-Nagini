from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def incr__list(l : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(l)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(l)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (len(l)))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(l)))) or (((Result())[i]) == (((l)[i]) + (1)))))
    # post-conditions-end

    # impl-start
    result : List[int] = list([])
    i : int = 0
    while (i) < (len(l)):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(l)))
        Invariant(((0) <= (i)) and ((i) <= (len(l))))
        Invariant((len(result)) == (i))
        Invariant(Forall(int, lambda i1:
            not (((0) <= (i1)) and ((i1) < (i))) or (((result)[i1]) == (((l)[i1]) + (1)))))
        # invariants-end
        result = (result) + ([((l)[i]) + (1)])
        i = (i) + (1)
    return result
    # impl-end
