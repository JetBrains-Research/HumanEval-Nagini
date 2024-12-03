from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def PluckSmallestEven(nodes : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(nodes)))
    Requires((len(nodes)) <= (10000))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(nodes)))) or (((nodes)[i]) >= (0))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(nodes)))
    Ensures(Acc(list_pred(Result())))
    Ensures(((len(Result())) == (0)) or ((len(Result())) == (2)))
    Ensures(not ((len(Result())) == (2)) or ((((0) <= ((Result())[1])) and (((Result())[1]) < (len(nodes)))) and (((nodes)[(Result())[1]]) == ((Result())[0]))))
    Ensures(not ((len(Result())) == (2)) or ((((Result())[0] % 2)) == (0)))
    Ensures(not ((len(Result())) == (2)) or (Forall(int, lambda i:
        not ((((0) <= (i)) and ((i) < (len(nodes)))) and ((((nodes)[i] % 2)) == (0))) or (((Result())[0]) <= ((nodes)[i])))))
    Ensures(not ((len(Result())) == (2)) or (Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < ((Result())[1]))) or (((((nodes)[i] % 2)) != (0)) or (((nodes)[i]) > ((Result())[0]))))))
    Ensures(not ((len(Result())) == (0)) or (Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(nodes)))) or ((((nodes)[i] % 2)) != (0)))))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    smallestEven : int = -1
    smallestIndex : int = -1
    i : int = int(0)
    while i < len(nodes):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(nodes)))
        Invariant(((0) <= (i)) and ((i) <= (len(nodes))))
        Invariant(((smallestEven) == (-1)) == ((smallestIndex) == (-1)))
        Invariant(not ((smallestIndex) != (-1)) or (((0) <= (smallestIndex)) and ((smallestIndex) < (i))))
        Invariant(not ((smallestIndex) != (-1)) or (((nodes)[smallestIndex]) == (smallestEven)))
        Invariant(not ((smallestEven) != (-1)) or (((smallestEven % 2)) == (0)))
        Invariant(not ((smallestEven) != (-1)) or (Forall(int, lambda j:
            (not ((((0) <= (j)) and ((j) < (i))) and ((((nodes)[j] % 2)) == (0))) or ((smallestEven) <= ((nodes)[j])), [[(nodes)[j]]]))))
        Invariant(not ((smallestIndex) != (-1)) or (Forall(int, lambda j:
            (not (((0) <= (j)) and ((j) < (smallestIndex))) or ((((nodes)[j] % 2)) != (0)) or (((nodes)[j]) > (smallestEven)), [[(nodes)[j]]]))))
        Invariant(not ((smallestIndex) == (-1)) or (Forall(int, lambda j:
            (not (((0) <= (j)) and ((j) < (i))) or ((((nodes)[j] % 2)) != (0)), [[(nodes)[j]]]))))
        # invariants-end
        if ((((nodes)[i] % 2)) == (0)) and (((smallestEven) == (-1)) or (((nodes)[i]) < (smallestEven))):
            smallestEven = (nodes)[i]
            smallestIndex = i
        i = i + 1
    if (smallestIndex) == (-1):
        result = list([])
        return result
    else:
        result = list([smallestEven, smallestIndex])
        return result
    # impl-end
