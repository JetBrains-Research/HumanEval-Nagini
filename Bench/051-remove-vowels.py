from typing import List
from nagini_contracts.contracts import *

def remove__vowels(text : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(text)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(text)))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(Result())))) or (((((((Result())[i]) != (0)) and (((Result())[i]) != (1))) and (((Result())[i]) != (2))) and (((Result())[i]) != (3))) and (((Result())[i]) != (4)))))
    Ensures(Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(Result())))) or (((Result())[i]) in (text))))
    Ensures(Forall(int, lambda j:
        not ((((((((j) >= (0)) and ((j) < (len(text)))) and (((text)[j]) != (0))) and (((text)[j]) != (1))) and (((text)[j]) != (2))) and (((text)[j]) != (3))) and (((text)[j]) != (4))) or (((text)[j]) in (Result()))))
    # post-conditions-end

    # impl-start
    s : List[int] = []
    i : int = 0
    while (i) < (len(text)):
        # invariants-start
        Invariant(Acc(list_pred(text)))
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= (len(text))))
        Invariant(Forall(int, lambda i:
            not (((i) >= (0)) and ((i) < (len(s)))) or (((((((s)[i]) != (0)) and (((s)[i]) != (1))) and (((s)[i]) != (2))) and (((s)[i]) != (3))) and (((s)[i]) != (4)))))
        Invariant(Forall(int, lambda i:
            not (((i) >= (0)) and ((i) < (len(s)))) or (((s)[i]) in (text))))
        Invariant(Forall(int, lambda j:
            not ((((((((j) >= (0)) and ((j) < (i))) and (((text)[j]) != (0))) and (((text)[j]) != (1))) and (((text)[j]) != (2))) and (((text)[j]) != (3))) and (((text)[j]) != (4))) or (((text)[j]) in (s))))
        # invariants-end
        c : int = (text)[i]
        if (((((c) != (0)) and ((c) != (1))) and ((c) != (2))) and ((c) != (3))) and ((c) != (4)):
            s = (s) + [c]
        i = (i) + (1)
    return s
    # impl-end
