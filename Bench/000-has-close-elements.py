from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *


def abs_value(val: int) -> int:
    # post-conditions-start
    Ensures(Implies(val < 0, Result() == -val))
    Ensures(Implies(val >= 0, Result() == val))
    # post-conditions-end
    # impl-start
    if val < 0:
        return -val
    else:
        return val
    # impl-end


@Pure
def abs1(x: int, threshold: int) -> bool:
    # pure-start
    return x >= threshold or x <= -threshold
    # pure-end

@Pure
def fn(x: int, numbers: List[int], threshold: int) -> bool:
    # pure-pre-conditions-start
    Requires(threshold > 0)
    Requires(Acc(list_pred(numbers)))
    Requires(x >= 0 and x < len(numbers))
    # pure-pre-conditions-end

    # pure-start
    return Forall(range(len(numbers)), lambda y :
        x == y or
        abs1(numbers[x] - numbers[y], threshold)
    )
    # pure-end


def has_close_elements(numbers: List[int], threshold: int) -> bool:
    # pre-conditions-start
    Requires(threshold > 0)
    Requires(Acc(list_pred(numbers)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Implies(Result() != True, Forall(range(len(numbers)), lambda x : 
            fn(x, numbers, threshold)
    )))
    # post-conditions-end
    
    # impl-start
    flag = False
    i = 0
    while i < len(numbers):
        # invariants-start
        Invariant(Acc(list_pred(numbers)))
        Invariant(0 <= i and i <= len(numbers))
        Invariant(Implies(flag != True, 
            Forall(range(i), lambda x : fn(x, numbers, threshold))))
        # invariants-end
        j = 0
        while j < len(numbers):
            # invariants-start
            Invariant(Acc(list_pred(numbers)))
            Invariant(0 <= i and i < len(numbers))
            Invariant(0 <= j and j <= len(numbers))
            
            Invariant(
                Implies(
                    flag != True, 
                    Forall(range(i), lambda x : fn(x, numbers, threshold)) and 
                        Forall(range(j), lambda y : i == y or abs1(numbers[i] - numbers[y], threshold))
                    )
                )
            # invariants-end
            
            if i != j:
                distance = abs_value(numbers[i] - numbers[j])
                if distance < threshold:
                    flag = True
            
            j += 1
        i += 1

    return flag
    # impl-end
