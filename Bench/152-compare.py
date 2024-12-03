from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def Compare(scores : List[int], guesses : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(guesses)))
    Requires(Acc(list_pred(scores)))
    Requires((len((scores))) == (len((guesses))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(guesses)))
    Ensures(Acc(list_pred(scores)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len((Result()))) == (len((scores))))
    Ensures((len((scores))) == (len((guesses))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len((Result()))))) or (((Result())[i]) == (abs(((scores)[i]) - ((guesses)[i]))))))
    # post-conditions-end

    # impl-start
    result : List[int] = [int(0)] * len((scores))
    i : int = 0
    while (i) < (len((scores))):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(guesses)))
        Invariant(Acc(list_pred(scores)))
        Invariant(((0) <= (i)) and ((i) <= (len((scores)))))
        Invariant((len((result))) == (len((scores))))
        Invariant((len((scores))) == (len((guesses))))
        Invariant(Forall(int, lambda k:
            not (((0) <= (k)) and ((k) < (i))) or (((result)[k]) == (abs(((scores)[k]) - ((guesses)[k]))))))
        # invariants-end
        (result)[(i)] = abs(((scores)[i]) - ((guesses)[i]))
        i = (i) + (1)
    return result
    # impl-end

@Pure
def abs(x : int) -> int :
    # pure-start
    if (x) < (0):
        return (0) - (x)
    elif True:
        return x
    # pure-end
