from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def monotonic(xs : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(xs)))
    Requires((len(xs)) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(xs)))
    Ensures((Result()) == ((Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((0) <= (i)) and ((i) < (j))) and ((j) < (len(xs)))) or (((xs)[i]) < ((xs)[j]))))) or (Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((0) <= (i)) and ((i) < (j))) and ((j) < (len(xs)))) or (((xs)[i]) > ((xs)[j])))))))
    # post-conditions-end

    # impl-start
    if (len(xs)) == (1):
        return True
    increasing : bool = True
    decreasing : bool = True
    i : int = 1
    while (i) < (len(xs)):
        # invariants-start
        Invariant(Acc(list_pred(xs)))
        Invariant(((1) <= (i)) and ((i) <= (len(xs))))
        Invariant((increasing) == (Forall(int, lambda j:
            Forall(int, lambda k:
                not ((((0) <= (j)) and ((j) < (k))) and ((k) < (i))) or (((xs)[j]) < ((xs)[k]))))))
        Invariant((decreasing) == (Forall(int, lambda j:
            Forall(int, lambda k:
                not ((((0) <= (j)) and ((j) < (k))) and ((k) < (i))) or (((xs)[j]) > ((xs)[k]))))))
        # invariants-end
        if ((xs)[(i) - (1)]) >= ((xs)[i]):
            increasing = False
        if ((xs)[(i) - (1)]) <= ((xs)[i]):
            decreasing = False
        i = (i) + (1)
    result : bool = (increasing) or (decreasing)
    return result
    # impl-end
