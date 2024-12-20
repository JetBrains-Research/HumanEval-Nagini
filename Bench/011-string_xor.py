from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def xor(a : int, b : int) -> int:
    # pure-pre-conditions-start
    Ensures((Result()) == ((0 if (a) == (b) else 1)))
    # pure-pre-conditions-end

    # pure-start
    result : int = int(0)
    if (a) == (b):
        result = 0
    else:
        result = 1
    return result
    # pure-end

def string__xor(a : List[int], b : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(b)))
    Requires(Acc(list_pred(a)))
    Requires((len(a)) == (len(b)))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(a)))) or ((((a)[i]) == (0)) or (((a)[i]) == (1)))))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(b)))) or ((((b)[i]) == (0)) or (((b)[i]) == (1)))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(b)))
    Ensures(Acc(list_pred(a)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(a)) == (len(b)))
    Ensures((len(Result())) == (len(a)))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or ((((Result())[i]) == (0)) or (((Result())[i]) == (1)))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or (((Result())[i]) == ((0 if ((a)[i]) == ((b)[i]) else 1)))))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    i : int = int(0)
    while (i) < (len(a)):
        # invariants-start
        Invariant(Acc(list_pred(b)))
        Invariant(Acc(list_pred(a)))
        Invariant(Acc(list_pred(result))) 
        Invariant((len(a)) == (len(b)))
        Invariant(((i) >= (0)) and ((i) <= (len(a))))
        Invariant((len(result)) == (i))
        Invariant(Forall(int, lambda i:
            not (((0) <= (i)) and ((i) < (len(a)))) or ((((a)[i]) == (0)) or (((a)[i]) == (1)))))
        Invariant(Forall(int, lambda i:
            not (((0) <= (i)) and ((i) < (len(b)))) or ((((b)[i]) == (0)) or (((b)[i]) == (1)))))
        Invariant(Forall(int, lambda j:
            not (((0) <= (j)) and ((j) < (i))) or (((result)[j]) == ((0 if ((a)[j]) == ((b)[j]) else 1)))))
        # invariants-end
        bitResult = (0 if ((a)[i]) == ((b)[i]) else 1)
        result = (result) + [bitResult]
        i = (i) + (1)
    return result
    # impl-end
