from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def pairs__sum__to__zero(l : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(l)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(l)))
    Ensures(not (Result()) or (Exists(int, lambda i:
        Exists(int, lambda j:
            (((((0) <= (i)) and ((i) < (len(l)))) and (((0) <= (j)) and ((j) < (len(l))))) and ((i) != (j))) and ((((l)[i]) + ((l)[j])) == (0))))))
    Ensures(not (not(Result())) or (Forall(int, lambda i:
        Forall(int, lambda j:
            (not (((((0) <= (i)) and ((i) < (len(l)))) and (((0) <= (j)) and ((j) < (len(l))))) and ((i) != (j))) or ((((l)[i]) + ((l)[j])) != (0)), [[((l)[i]) + ((l)[j])]])))))
    # post-conditions-end

    # impl-start
    result : bool = False
    i : int = 0
    while (i) < (len(l)):
        # invariants-start
        Invariant(Acc(list_pred(l)))
        Invariant(((i) >= (0)) and ((i) <= (len(l))))
        Invariant(Implies(not(result), Forall(int, lambda i1:
            Forall(int, lambda j:
                (Implies(((((0) <= (i1)) and ((i1) < (i))) and (((0) <= (j)) and ((j) < (len(l))))) and ((i1) != (j)), (((l)[i1]) + ((l)[j])) != (0)), [[((l)[i1]) + ((l)[j])]])))))
        Invariant(not (result) or (Exists(int, lambda i1:
            Exists(int, lambda j:
                (((((0) <= (i1)) and ((i1) < (i))) and (((0) <= (j)) and ((j) < (len(l))))) and ((i1) != (j))) and ((((l)[i1]) + ((l)[j])) == (0))))))
        # invariants-end
        j : int = 0
        while (j) < (len(l)):
            # invariants-start
            Invariant(Acc(list_pred(l)))
            Invariant(((i) >= (0)) and ((i) < (len(l))))
            Invariant(((j) >= (0)) and ((j) <= (len(l))))
            Invariant(Implies(not(result), Forall(int, lambda i1:
                Forall(int, lambda j1:
                    (Implies((((((0) <= (i1)) and ((i1) < (i))) and (((0) <= (j1)) and ((j1) < (len(l))))) or (i1 == i and ((0) <= (j1)) and ((j1) < (j)))) and ((i1) != (j1)), (((l)[i1]) + ((l)[j1])) != (0)), [[((l)[i1]) + ((l)[j1])]])))))
            Invariant(not (result) or ((Exists(int, lambda i1:
                Exists(int, lambda j1:
                    (((((0) <= (i1)) and ((i1) < (i))) and (((0) <= (j1)) and ((j1) < (len(l))))) and ((i1) != (j1))) and ((((l)[i1]) + ((l)[j1])) == (0)))))
             or (Exists(int, lambda j1:
                ((((0) <= (j1)) and ((j1) < (j))) and ((i) != (j1))) and ((((l)[i]) + ((l)[j1])) == (0))))))
            # invariants-end
            if ((i) != (j)) and ((((l)[i]) + ((l)[j])) == (0)):
                result = True
            j = (j) + (1)
        i = (i) + (1)
    return result
    # impl-end
