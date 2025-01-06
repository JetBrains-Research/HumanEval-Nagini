from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def min(a : int, b : int) -> int :
    # pure-start
    if (a) <= (b):
        return a
    elif True:
        return b
    # pure-end

#use-as-unpure
@Pure
def max(a : int, b : int) -> int :
    # pure-start
    if (a) >= (b):
        return a
    elif True:
        return b
    # pure-end

def generate__integers(a : int, b : int) -> List[int]:
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(Result())))) or ((((Result())[i] % 2)) == (0))))
    Ensures(Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(Result())))) or (((Result())[i]) > 0 and ((Result())[i]) < 10)))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    left : int = min(a, b)
    right : int = max(a, b)
    lower : int = max(2, left)
    upper : int = min(8, right)
    i : int = lower
    
    while (i) <= (upper):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(i >= 2)
        Invariant(Implies((i) <= (upper), i <= 8))
        Invariant(upper <= 8)
        Invariant(Forall(int, lambda j:
            (not (((j) >= (0)) and ((j) < (len(result)))) or ((((result)[j] % 2)) == (0)))))
        Invariant(Forall(int, lambda j:
            (not (((j) >= (0)) and ((j) < (len(result)))) or (((result)[j]) > 0 and ((result)[j]) < 10), [[result[j]]])))
        # invariants-end
        if ((i % 2)) == (0):
            result = (result) + (([i]))
        i = (i) + (1)
    return result
    # impl-end
