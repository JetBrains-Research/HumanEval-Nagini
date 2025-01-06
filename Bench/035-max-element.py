from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def max__element(l : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(l)))
    Requires((len(l)) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(l)))
    Ensures(Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(l)))) or (((l)[i]) <= (Result()))))
    Ensures(Exists(int, lambda i:
        (((i) >= (0)) and ((i) < (len(l)))) and (((l)[i]) == (Result()))))
    # post-conditions-end

    # impl-start
    result : int = (l)[0]
    i : int = 1
    while (i) < (len(l)):
        # invariants-start
        Invariant(Acc(list_pred(l)))
        Invariant(((i) >= (1)) and ((i) <= (len(l))))
        Invariant(Forall(int, lambda i1:
            not (((i1) >= (0)) and ((i1) < (i))) or (((l)[i1]) <= (result))))
        Invariant(Exists(int, lambda i1:
            (((i1) >= (0)) and ((i1) < (i))) and (((l)[i1]) == (result))))
        # invariants-end
        if ((l)[i]) > (result):
            result = (l)[i]
        i = (i) + (1)
    return result
    # impl-end
