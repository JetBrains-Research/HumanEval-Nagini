from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def NotInArray(a : List[int], x : int) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    # pre-conditions-end

    # pure-start
    return Forall(int, lambda i:
        (Implies(((0) <= (i)) and ((i) < (len((a)))), ((a)[i]) != (x)), [[(a)[i]]]))
    # pure-end

@Pure 
def ExistsBoth(a : List[int], b : List[int], x : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    Requires(Acc(list_pred(b), 1/2))
    # pre-conditions-end
    
    # pure-start
    return Exists(int, lambda i:
        (Implies(((0) <= (i)) and ((i) < (len((a)))), ((a)[i]) == (x)))) and Exists(int, lambda i:
        (Implies(((0) <= (i)) and ((i) < (len((b)))), ((b)[i]) == (x))))
    # pure-end

def common(l1 : List[int], l2 : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(l2), 1/2))
    Requires(Acc(list_pred(l1), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(l2), 1/2))
    Ensures(Acc(list_pred(l1), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda j:
        (Implies(((j) >= 0 and j < len(l1)), Implies((Exists(int, lambda x: x >= 0 and  x< len(l2) and l2[x] == l1[j])), Exists(int, lambda x: x >= 0 and  x< len(Result()) and Result()[x] == l1[j]))))))
    # post-conditions-end

    # impl-start
    c : List[int] = []
    i : int = 0
    while (i) < (len(l1)):
        # invariants-start
        Invariant(Acc(list_pred(c)))
        Invariant(Acc(list_pred(l2), 1/2))
        Invariant(Acc(list_pred(l1), 1/2))
        Invariant(((i) >= (0)) and ((i) <= (len(l1))))
        Invariant(Forall(int, lambda j:
            (Implies(((j) >= 0 and j < i), Implies((Exists(int, lambda x: x >= 0 and  x< len(l2) and l2[x] == l1[j])), Exists(int, lambda x: x >= 0 and  x< len(c) and c[x] == l1[j]))), 
                [[l1[j]]])))
        Invariant(Forall(int, lambda i: 
            (Implies((i) >= 0 and i < len(c), ExistsBoth(l1, l2, c[i])), [[ExistsBoth(l1, l2, c[i])]])))
        # invariants-end
        j : int = 0
        while (j) < (len(l2)):
            # invariants-start
            Invariant(Acc(list_pred(c)))
            Invariant(Acc(list_pred(l2), 1/2))
            Invariant(Acc(list_pred(l1), 1/2))
            Invariant(((i) >= (0)) and ((i) < (len(l1))))
            Invariant(((j) >= (0)) and ((j) <= (len(l2))))
            Invariant(Forall(int, lambda j:
                (Implies(((j) >= 0 and j < i), Implies((Exists(int, lambda x: x >= 0 and  x< len(l2) and l2[x] == l1[j])), Exists(int, lambda x: x >= 0 and  x< len(c) and c[x] == l1[j]))), 
                    [[l1[j]]])))
            Invariant(Implies(Exists(int, lambda x: x >= 0 and  x < j and l2[x] == l1[i]), Exists(int, lambda x: x >= 0 and  x < len(c) and c[x] == l1[i])))
            Invariant(Forall(int, lambda i: 
                (Implies((i) >= 0 and i < len(c), ExistsBoth(l1, l2, c[i])), [[ExistsBoth(l1, l2, c[i])]])))
            # invariants-end
            if ((l1)[i]) == ((l2)[j]) and NotInArray(c, (l1)[i]):
                c = c + [((l1)[i])]
                # assert-start
                Assert((Exists(int, lambda x : x >= 0 and x < len(l1) and (c[len(c) - 1]) == (l1[x]))))
                Assert((Exists(int, lambda x : x >= 0 and x < len(l2) and (c[len(c) - 1]) == (l2[x]))))
                Assert(ExistsBoth(l1, l2, c[len(c) - 1]))
                # assert-end
            j = (j) + (1)
        i = (i) + (1)
    return c
    # impl-end
