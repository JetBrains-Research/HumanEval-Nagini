from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def getVal(mx: Optional[int]) -> int:
    # pre-conditions-start
    Requires(mx is not None)
    # pre-conditions-end
    # impl-start
    return mx
    # impl-end

def rolling_max(numbers: List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(numbers)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(numbers)))
    Ensures(Acc(list_pred(Result())))
    Ensures(len(Result()) == len(numbers))
    Ensures(Forall(range(len(numbers)), lambda i: numbers[i] <= Result()[i]))
    Ensures(Forall(range(len(numbers) - 1), lambda i: Result()[i] <= Result()[i + 1]))
    # post-conditions-end

    # impl-start
    running_max : Optional[int] = None
    result : List[int] = []

    i = 0
    while i < len(numbers):
        # invariants-start
        Invariant(Acc(list_pred(numbers)))
        Invariant(Acc(list_pred(result)))
        Invariant(0 <= i and i <= len(numbers))
        Invariant(len(result) == i)
        Invariant(Forall(range(i), lambda i1: numbers[i1] <= result[i1]))
        Invariant(Old(running_max) is None or ((Old(running_max) is not None) and (getVal(Old(running_max)) <= getVal(running_max))))
        Invariant(Implies(len(result) > 0, running_max is not None))
        Invariant(Implies(len(result) > 0, result[-1] == getVal(running_max)))
        Invariant(Forall(range(i - 1), lambda i1: result[i1] <= result[i1 + 1]))
        # invariants-end

        n = numbers[i]
        if running_max is None or running_max < n:
            running_max = n
        
        result.append(running_max)
        i += 1

    return result
    # impl-end