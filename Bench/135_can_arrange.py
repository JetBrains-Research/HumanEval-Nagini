from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def can__arrange(arr : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(arr)))
    Requires((len(arr)) > (0))
    Requires(Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((0) <= (i)) and ((i) < (j))) and ((j) < (len(arr)))) or (((arr)[i]) != ((arr)[j])))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(arr)))
    Ensures(not ((Result()) == (-1)) or (Forall(int, lambda i:
        not (((1) <= (i)) and ((i) < (len(arr)))) or (((arr)[i]) >= ((arr)[(i) - (1)])))))
    Ensures(not ((Result()) >= (0)) or ((((1) <= (Result())) and ((Result()) < (len(arr)))) and (((arr)[Result()]) < ((arr)[(Result()) - (1)]))))
    Ensures(not ((Result()) >= (0)) or (Forall(int, lambda i:
        not (((Result()) < (i)) and ((i) < (len(arr)))) or (((arr)[i]) >= ((arr)[(i) - (1)])))))
    # post-conditions-end

    # impl-start
    i : int = 1
    pos : int = -1
    while (i) < (len(arr)):
        # invariants-start
        Invariant(Acc(list_pred(arr)))
        Invariant(((1) <= (i)) and ((i) <= (len(arr))))
        Invariant(not ((pos) == (-1)) or (Forall(int, lambda j:
            not (((1) <= (j)) and ((j) < (i))) or (((arr)[j]) >= ((arr)[(j) - (1)])))))
        Invariant(not ((pos) >= (0)) or ((((1) <= (pos)) and ((pos) < (i))) and (((arr)[pos]) < ((arr)[(pos) - (1)]))))
        Invariant(not ((pos) >= (0)) or (Forall(int, lambda j:
            not (((pos) < (j)) and ((j) < (i))) or (((arr)[j]) >= ((arr)[(j) - (1)])))))
        # invariants-end
        if ((arr)[i]) < ((arr)[(i) - (1)]):
            pos = i
        i = (i) + (1)
    return pos
    # impl-end

