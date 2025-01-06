from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def sorted__even(a : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    Requires((len(a)) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (len(a)))
    Ensures(Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((((0) <= (i)) and ((i) < (j))) and ((j) < (len(Result())))) and (((i % 2)) == (0))) and (((j % 2)) == (0))) or (((Result())[i]) <= ((Result())[j])))))
    Ensures(Forall(int, lambda i:
        not ((((0) <= (i)) and ((i) < (len(a)))) and (((i % 2)) == (1))) or (((Result())[i]) == ((a)[i]))))
    # post-conditions-end

    # impl-start
    sorted__even : List[int] =[]
    p : List[bool] = []
    i : int = 0
    while (i) < (len(a)):
        # invariants-start
        Invariant(Acc(list_pred(p)))
        Invariant(Acc(list_pred(sorted__even)))
        Invariant(Acc(list_pred(a)))
        Invariant(((0) <= (i)) and ((i) <= (len(a))))
        Invariant((len(p)) == (i))
        Invariant(Forall(int, lambda j:
            not (((0) <= (j)) and ((j) < (i))) or (((p)[j]) == (((j % 2)) == (0)))))
        # invariants-end    
        p = (p) + [((i % 2)) == (0)]
        i = (i) + (1)
    sorted__even = SortSeqPred(a, p)
    return sorted__even
    # impl-end

def SortSeqPred(s : List[int], p : List[bool]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(p), 1/2))
    Requires(Acc(list_pred(s), 1/2))
    Requires((len(s)) == (len(p)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(p), 1/2))
    Ensures(Acc(list_pred(s), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(s)) == (len(p)))
    Ensures((len(Result())) == (len(s)))
    Ensures(Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((((0) <= (i)) and ((i) < (j))) and ((j) < (len(Result())))) and ((p)[i])) and ((p)[j])) or (((Result())[i]) <= ((Result())[j])))))
    Ensures(Forall(int, lambda i:
        not ((((0) <= (i)) and ((i) < (len(s)))) and (not((p)[i]))) or (((Result())[i]) == ((s)[i]))))
    # post-conditions-end

    # impl-start
    sorted : List[int] = list(s)
    i : int = 0
    while (i) < (len(sorted)):
        # invariants-start
        Invariant(Acc(list_pred(sorted)))
        Invariant(Acc(list_pred(p), 1/2))
        Invariant(Acc(list_pred(s), 1/2))
        Invariant((len(s)) == (len(p)))
        Invariant(((0) <= (i)) and ((i) <= (len(sorted))))
        Invariant((len(sorted)) == (len(s)))
        Invariant(Forall(int, lambda j:
            not ((((0) <= (j)) and ((j) < (len(s)))) and (not((p)[j]))) or (((sorted)[j]) == ((s)[j]))))
        Invariant(Forall(int, lambda j:
            (Forall(int, lambda k:
                (not ((((((0) <= (j)) and ((j) < (k))) and ((k) < (i))) and ((p)[j])) and ((p)[k])) or 
                (((sorted)[j]) <= ((sorted)[k])), [[(sorted)[k]]])), [[sorted[j]]])))
        Invariant(Forall(int, lambda j:
            (not ((((0) <= (j)) and ((j) < (i))) and ((p)[j])) or 
                (Forall(int, lambda k:
                    (not ((((i) <= (k)) and ((k) < (len(sorted)))) and ((p)[k])) or 
                        (((sorted)[j]) <= ((sorted)[k])), [[sorted[k]]]))), [[(sorted)[j]]])))
        # invariants-end
        if (p)[i]:
            minIndex : int = i
            j : int = (i) + (1)
            while (j) < (len(sorted)):
                # invariants-start
                Invariant(Acc(list_pred(sorted)))
                Invariant(Acc(list_pred(p), 1/2))
                Invariant(Acc(list_pred(s), 1/2))
                Invariant((len(s)) == (len(p)))
                Invariant((len(sorted)) == (len(s)))
                Invariant(0 <= i and i < len(sorted))
                Invariant((((i) <= (minIndex)) and ((minIndex) < (j))) and ((j) <= (len(sorted))))
                Invariant(p[i])
                Invariant((p)[minIndex])
                Invariant(Forall(int, lambda k:
                    not ((((i) <= (k)) and ((k) < (j))) and ((p)[k])) or (((sorted)[minIndex]) <= ((sorted)[k]))))
                Invariant(Forall(int, lambda j:
                    not ((((0) <= (j)) and ((j) < (len(s)))) and (not((p)[j]))) or (((sorted)[j]) == ((s)[j]))))
                Invariant(Forall(int, lambda j:
                    (Forall(int, lambda k:
                        (not ((((((0) <= (j)) and ((j) < (k))) and ((k) < (i))) and ((p)[j])) and ((p)[k])) or 
                        (((sorted)[j]) <= ((sorted)[k])), [[(sorted)[k]]])), [[sorted[j]]])))
                Invariant(Forall(int, lambda j:
                    (not ((((0) <= (j)) and ((j) < (i))) and ((p)[j])) or 
                        (Forall(int, lambda k:
                            (not ((((i) <= (k)) and ((k) < (len(sorted)))) and ((p)[k])) or 
                                (((sorted)[j]) <= ((sorted)[k])), [[sorted[k]]]))), [[(sorted)[j]]])))
                # invariants-end
                if ((p)[j]) and (((sorted)[j]) < ((sorted)[minIndex])):
                    minIndex = j
                j = (j) + (1)
            if (minIndex) != (i):
                # assert-start
                Assert((p)[minIndex])
                Assert(p[i])
                # assert-end
                rhs0_ : int = (sorted)[i]
                (sorted)[i] = (sorted)[minIndex]
                (sorted)[minIndex] = rhs0_
        i = (i) + (1)
    return sorted
    # impl-end
