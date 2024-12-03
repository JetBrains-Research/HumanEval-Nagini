from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def strange__sort__list__helper(s : List[int]) -> Tuple[List[int], List[int]]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result()[0])))
    Ensures(Acc(list_pred(Result()[1])))
    Ensures(Forall(int, lambda i:
        Forall(int, lambda j:
            Implies((((0) <= (i)) and ((i) < (j))) and ((j) < (len((Result()[0])))), ((Result()[0])[i]) <= ((Result()[0])[j])))))
    Ensures(((len(s)) == (len(Result()[0]))) and ((len(Result()[0])) == (len(Result()[1]))))
    Ensures(Forall(int, lambda i:
        not ((((0) <= (i)) and ((i) < (len(s)))) and (((i % 2)) == (0))) or (((Result()[1])[i]) == ((Result()[0])[(i // 2)]))))
    Ensures(Forall(int, lambda i:
        not ((((0) <= (i)) and ((i) < (len(s)))) and (((i % 2)) == (1))) or (((Result()[1])[i]) == ((Result()[0])[((len(s)) - ((((i) - (1)) // 2))) - (1)]))))
    # post-conditions-end

    # impl-start
    sorted : List[int] = BubbleSort(s)
    strange : List[int] = list(s)
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(strange)))
        Invariant(Acc(list_pred(sorted)))
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant(len(sorted) == len(s))
        Invariant((len(strange)) == len(s))
        Invariant(Forall(int, lambda i:
            Forall(int, lambda j:
                Implies((((0) <= (i)) and ((i) < (j))) and ((j) < (len((sorted)))), ((sorted)[i]) <= ((sorted)[j])))))
        Invariant(Forall(int, lambda j:
            (Implies((((0) <= (j)) and ((j) < (i))) and (((j % 2)) == (0)), ((strange)[j]) == ((sorted)[(j // 2)])), [[(strange)[j]]])))
        Invariant(Forall(int, lambda j:
            (Implies((((0) <= (j)) and ((j) < (i))) and (((j % 2)) == (1)), ((strange)[j]) == ((sorted)[((len(s)) - ((((j) - (1)) // 2))) - (1)])), [[(strange)[j]]])))
        # invariants-end
        if ((i % 2)) == (0):
            strange[i] = (sorted)[(i // 2)]
        else:
            r : int = (((i) - (1)) // 2)
            strange[i] = (sorted)[((len(s)) - (r)) - (1)]
        i = (i) + (1)
    return (sorted, strange)
    # impl-end

def strange__sort__list(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(s)) == (len(Result())))
    # post-conditions-end

    # impl-start
    p : Tuple[List[int], List[int]] = strange__sort__list__helper(s)
    return p[1]
    # impl-end

def BubbleSort(a1 : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(a1)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a1)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(a1)) == (len(Result())))
    Ensures(Forall(int, lambda i:
        Forall(int, lambda j:
            Implies((((0) <= (i)) and ((i) < (j))) and ((j) < (len((Result())))), ((Result())[i]) <= ((Result())[j])))))
    # post-conditions-end

    # impl-start
    a : List[int] = list(a1)
    i : int = (len((a))) - (1)
    while (i) > (0):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(Acc(list_pred(a1)))
        Invariant((len(a1)) == (len(a)))
        Invariant(not ((i) < (0)) or ((len((a))) == (0)))
        Invariant(((-1) <= (i)) and ((i) < (len((a)))))
        Invariant(Forall(int, lambda ii:
            (Forall(int, lambda jj:
                (Implies((((i) <= (ii)) and ((ii) < (jj))) and ((jj) < (len((a)))), ((a)[ii]) <= ((a)[jj])),
                    [[(a)[jj]]])),
                [[(a)[ii]]])))
        Invariant(Forall(int, lambda k:
            (Forall(int, lambda k_k:
                (Implies(((((0) <= (k)) and ((k) <= (i))) and ((i) < (k_k)) and (k_k) < (len((a)))), ((a)[k]) <= ((a)[k_k])),
                    [[(a)[k_k]]])),
                [[(a)[k]]])))
        # invariants-end
        j : int = 0
        while (j) < (i):
            # invariants-start
            Invariant(Acc(list_pred(a)))
            Invariant(Acc(list_pred(a1)))
            Invariant((len(a1)) == (len(a)))
            Invariant((((0) < (i)) and ((i) < (len((a))))) and (((0) <= (j)) and ((j) <= (i))))
            Invariant(Forall(int, lambda ii:
                (Forall(int, lambda jj:
                    (Implies((((i) <= (ii)) and ((ii) <= (jj))) and ((jj) < (len((a)))), ((a)[ii]) <= ((a)[jj])),
                        [[(a)[jj]]])),
                    [[(a)[ii]]])))
            Invariant(Forall(int, lambda k:
                (Forall(int, lambda k_k:
                    (Implies(((((0) <= (k)) and ((k) <= (i))) and ((i) < (k_k))) and ((k_k) < (len((a)))), ((a)[k]) <= ((a)[k_k])),
                        [[(a)[k_k]]])),
                    [[(a)[k]]])))
            Invariant(Forall(int, lambda k:
                (Implies(((0) <= (k)) and ((k) <= (j)), ((a)[k]) <= ((a)[j])),
                    [[(a)[k]]])))
            # invariants-end
            if ((a)[j]) > ((a)[(j) + (1)]):
                rhs0_ : int = (a)[(j) + (1)]
                (a)[(j) + (1)] = (a)[j]
                (a)[j] = rhs0_
            j = (j) + (1)
        i = (i) - (1)
    return a
    # impl-end
