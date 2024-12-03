from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *


def is__sorted(a : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a)))
    Ensures((Result()) == (
        Forall(int, lambda i:
            Forall(int, lambda j:
                not ((((0) <= (i)) and ((i) <= (j))) and ((j) < (len(a)))) or ((((a)[i]) <= ((a)[j])))))
        and (Forall(int, lambda i:
                    not (((0) <= (i)) and ((i) < (len(a)))) or ((count_set(a, (a)[i], 0)) <= (2))))))
    # post-conditions-end
    # impl-start
    if (len(a)) == (0):
        # assert-start
        Assert(Forall(int, lambda i:
            Forall(int, lambda j:
                not ((((0) <= (i)) and ((i) <= (j))) and ((j) < (len(a)))) or ((((a)[i]) <= ((a)[j]))))))
        # assert-end
        return True
    is__asc : bool = True
    i : int = 1
    while (i) < (len(a)):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(((1) <= (i)) and ((i) <= (len(a))))
        Invariant((is__asc) == (Forall(int, lambda j:
            Forall(int, lambda k:
                not ((((0) <= (j)) and ((j) < (k))) and ((k) < (i))) or (((a)[j]) <= ((a)[k]))))))
        # invariants-end
        if ((a)[(i) - (1)]) > ((a)[i]):
            is__asc = False
        i = (i) + (1)
    if not(is__asc):
        return False
    i = 0
    has__no__more__that__2 : bool = True
    while (i) < (len(a)):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(((0) <= (i)) and ((i) <= (len(a))))
        Invariant((is__asc) == 
            (Forall(int, lambda j:
                Forall(int, lambda k:
                    not ((((0) <= (j)) and ((j) < (k))) and ((k) < (len(a)))) or (((a)[j]) <= ((a)[k]))))))
        Invariant((has__no__more__that__2) == (Forall(int, lambda j:
            not (((0) <= (j)) and ((j) < (i))) or ((count_set(a, (a)[j], 0)) <= (2))) and 
            (Forall(int, lambda j:
                Forall(int, lambda k:
                    not ((((0) <= (j)) and ((j) < (k))) and ((k) < (len(a)))) or (((a)[j]) <= ((a)[k])))))))
        # invariants-end
        count : int = count_set(a, (a)[i], 0)
        if (count) > (2):
            has__no__more__that__2 = False
        i = (i) + (1)
    f : bool = has__no__more__that__2
    return f
    # impl-end

@Pure
def count_set(a : List[int], x : int, i : int) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    Requires(((0) <= (i)) and ((i) <= (len(a))))
    # pre-conditions-end
    # post-conditions-start
    # post-conditions-end

    # pure-start
    if (i) == 0:
        return 0
    else:
        return (count_set(a, x, (i) - (1))) + (((a)[(i) - (1)]) == (x))
    # pure-end
