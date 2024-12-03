from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def is__sorted(a : List[int], l : int, r : int) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    Requires(((0) <= (l)) and ((l) <= (r)) and ((r) <= (len(a))))
    # pre-conditions-end
    
    # pure-start
    return Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((l) <= (i)) and ((i) < (j))) and ((j) < (r))) or (((a)[i]) <= ((a)[j]))))
    # pure-end

def move__one__ball(a : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    Requires((len(a)) > (0))
    Requires(Forall(int, lambda i:
        Forall(int, lambda j:
            not (((((0) <= (i)) and ((i) < (len(a)))) and (((0) <= (j)) and ((j) < (len(a))))) and ((i) != (j))) or (((a)[i]) != ((a)[j])))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a)))
    Ensures(Forall(int, lambda i:
        Forall(int, lambda j:
            not (((((0) <= (i)) and ((i) < (len(a)))) and (((0) <= (j)) and ((j) < (len(a))))) and ((i) != (j))) or (((a)[i]) != ((a)[j])))))
    Ensures(Implies(Result(), Exists(int, lambda i:
        (((0) <= (i)) and ((i) < (len(a)))) and (is__sorted(a, 0, i) and is__sorted(a, i, len(a)) and (Forall(int, lambda j:
            Implies(0 <= j and j < i, 
                Forall(int, lambda j1:
                    Implies(i <= j1 and j1 < len(a), a[j] > a[j1])))))))))
    Ensures(Implies(Exists(int, lambda i:
        (((0) <= (i)) and ((i) < (len(a)))) and (is__sorted(a, 0, i) and is__sorted(a, i, len(a)) and (Forall(int, lambda j:
            Implies(0 <= j and j < i, 
                Forall(int, lambda j1:
                    Implies(i <= j1 and j1 < len(a), a[j] > a[j1]))))))), Result()))
    # post-conditions-end

    # impl-start
    if (len(a)) <= (1):
        # assert-start
        Assert(is__sorted(a, 0, len(a)))
        # assert-end
        return True
    i : int = 0
    min__index : int = 0
    while (i) < (len(a)):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(((0) <= (i)) and ((i) <= (len(a))))
        Invariant(((0) <= (min__index)) and ((min__index) < (len(a))))
        Invariant(Forall(int, lambda i:
            (Forall(int, lambda j:
                (not (((((0) <= (i)) and ((i) < (len(a)))) and (((0) <= (j)) and ((j) < (len(a))))) and ((i) != (j))) or (((a)[i]) != ((a)[j]))
                 , [[(a)[j]]]))
                , [[a[i]]])))
        Invariant(Forall(int, lambda j:
            (not ((((0) <= (j)) and ((j) < (i))) and ((min__index) != (j))) or (((a)[min__index]) < ((a)[j])), [[(a)[j]]])))
        # invariants-end
        if ((a)[i]) < ((a)[min__index]):
            min__index = i
        i = (i) + (1)

    # assert-start
    Assert(Implies(is__sorted(a, 0, min__index) and is__sorted(a, min__index, len(a)) and min__index == 0, 
        is__sorted(a, 0, len(a))))
    Assert(Implies(is__sorted(a, 0, min__index) and is__sorted(a, min__index, len(a)) and min__index != 0 and a[len(a) - 1] < a[0], 
        (Forall(int, lambda j:
            Implies(0 <= j and j < min__index, 
                Forall(int, lambda j1:
                    Implies(min__index <= j1 and j1 < len(a), a[j] > a[j1])))))))
    # assert-end
    can : bool = is__sorted(a, 0, min__index) and is__sorted(a, min__index, len(a)) and (min__index == 0 or a[len(a) - 1] < a[0])
    return can
    # impl-end
