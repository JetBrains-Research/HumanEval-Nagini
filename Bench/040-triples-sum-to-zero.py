from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def triples__sum__to__zero(l : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(l)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(l)))
    Ensures(Implies(not(Result()), Forall(int, lambda i:
        Forall(int, lambda j:
            Forall(int, lambda k:
                Implies((((((((0) <= (i)) and ((i) < (len(l)))) and (((0) <= (j)) and ((j) < (len(l))))) and (((0) <= (k)) and ((k) < (len(l))))) and ((i) != (j))) and ((j) != (k))) and ((i) != (k)), ((((l)[i]) + ((l)[j])) + ((l)[k])) != (0)))))))
    Ensures(Implies(Result(), Exists(int, lambda i:
        Exists(int, lambda j:
            Exists(int, lambda k:
                ((((((((0) <= (i)) and ((i) < (len(l)))) and (((0) <= (j)) and ((j) < (len(l))))) and (((0) <= (k)) and ((k) < (len(l))))) and ((i) != (j))) and ((j) != (k))) and ((i) != (k))) and (((((l)[i]) + ((l)[j])) + ((l)[k])) == (0)))))))
    # post-conditions-end

    # impl-start
    i : int = 0
    while (i) < (len(l)):
        # invariants-start
        Invariant(Acc(list_pred(l), 1/2))
        Invariant(((i) >= (0)) and ((i) <= (len(l))))
        Invariant(Forall(int, lambda i1:
            Forall(int, lambda j:
                Forall(int, lambda k:
                    (Implies((((((((0) <= (i1)) and ((i1) < (i))) and (((0) <= (j)) and ((j) < (len(l))))) and (((0) <= (k)) and ((k) < (len(l))))) and ((i1) != (j))) and ((j) != (k))) and ((i1) != (k)), ((((l)[i1]) + ((l)[j])) + ((l)[k])) != (0)), [[(((l)[i1]) + ((l)[j])) + ((l)[k])]])))))
        # invariants-end
        j : int = 0
        while (j) < (len(l)):
            # invariants-start
            Invariant(Acc(list_pred(l), 1/2))
            Invariant(((i) >= (0)) and ((i) < (len(l))))
            Invariant(((j) >= (0)) and ((j) <= (len(l))))
            Invariant(Forall(int, lambda i1:
                Forall(int, lambda j1:
                    Forall(int, lambda k:
                        (Implies(((((((((0) <= (i1)) and ((i1) < (i))) and (((0) <= (j1)) and ((j1) < (len(l))))) and (((0) <= (k)) and ((k) < (len(l)))))) or
                                (i1 == i and (j1) >= 0 and (j1) < j and (k) >= 0 and (k) < len(l)))
                                and ((i1) != (j1)) and ((j1) != (k))) and ((i1) != (k)), ((((l)[i1]) + ((l)[j1])) + ((l)[k])) != (0)), [[(((l)[i1]) + ((l)[j1])) + ((l)[k])]])))))
            # invariants-end
            k : int = 0
            while (k) < (len(l)):
                # invariants-start
                Invariant(Acc(list_pred(l), 1/2))
                Invariant(((i) >= (0)) and ((i) < (len(l))))
                Invariant(((j) >= (0)) and ((j) < (len(l))))
                Invariant(((k) >= (0)) and ((k) <= (len(l))))
                Invariant(Forall(int, lambda i1:
                    Forall(int, lambda j1:
                        Forall(int, lambda k1:
                            (Implies(((((((((0) <= (i1)) and ((i1) < (i))) and (((0) <= (j1)) and ((j1) < (len(l))))) and (((0) <= (k1)) and ((k1) < (len(l)))))) or
                                (i1 == i and (j1) >= 0 and (j1) < j and (k1) >= 0 and (k1) < len(l)) or
                                (i1 == i and (j1) == j and (k1) >= 0 and (k1) < k))
                                and ((i1) != (j1)) and ((j1) != (k1))) and ((i1) != (k1)), ((((l)[i1]) + ((l)[j1])) + ((l)[k1])) != (0)), [[(((l)[i1]) + ((l)[j1])) + ((l)[k1])]])))))
                # invariants-end
                if ((((i) != (j)) and ((j) != (k))) and ((i) != (k))) and (((((l)[i]) + ((l)[j])) + ((l)[k])) == (0)):
                    return True
                k = (k) + (1)
            j = (j) + (1)
        i = (i) + (1)
    return False
    # impl-end
