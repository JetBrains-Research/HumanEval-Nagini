from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def below__threshold(l : List[int], t : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(l)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(l)))
    Ensures((Result()) == (Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(l)))) or (((l)[i]) < (t)))))
    # post-conditions-end

    # impl-start
    b : bool = True
    i : int = 0
    while (i) < (len(l)):
        # invariants-start
        Invariant(Acc(list_pred(l)))
        Invariant(((0) <= (i)) and ((i) <= (len(l))))
        Invariant((b) == (Forall(int, lambda i1:
            not (((i1) >= (0)) and ((i1) < (i))) or (((l)[i1]) < (t)))))
        # invariants-end
        if ((l)[i]) >= (t):
            b = False
        i = (i) + (1)
    return b
    # impl-end
