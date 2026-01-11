from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def InArray(a : List[int], x : int) -> bool:
    # pure-pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    # pure-pre-conditions-end

    # pure-start
    return Exists(int, lambda i:
        ((((0) <= (i)) and ((i) < (len((a)))) and ((a)[i]) == (x))))
    # pure-end



def uniqueSorted(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(Forall(int, lambda i:
        Forall(int, lambda j:
            Implies((((0) <= (i)) and ((i) < (j))) and ((j) < (len(s))), 
                ((s)[i]) <= ((s)[j])))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda k:
        (Implies(((0) <= (k)) and ((k) < (len(Result()))), InArray(s, Result()[k])))))
    Ensures(Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((0) <= (i)) and ((i) < (j))) and ((j) < (len(Result())))) or (((Result())[i]) < ((Result())[j])))))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(s), 1/2))
        Invariant(Forall(int, lambda i:
            Forall(int, lambda j:
                Implies((((0) <= (i)) and ((i) < (j))) and ((j) < (len(s))), 
                    ((s)[i]) <= ((s)[j])))))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant(Forall(int, lambda k:
            (Implies(((0) <= (k)) and ((k) < (len(result))), InArray(s, result[k])), [[InArray(s, result[k])]])))
        Invariant(Implies(i < len(s),
              Forall(int, lambda i1:
                (Implies(((0) <= (i1)) and ((i1) < len(result)), result[i1] <= s[i]), [[result[i1]]]))))
        Invariant(Forall(int, lambda k:
            (Forall(int, lambda l:
                (not ((((0) <= (k)) and ((k) < (l))) and ((l) < (len(result)))) or (((result)[k]) < ((result)[l])), 
                    [[(result)[l]]])), 
                [[(result)[k]]])))
        # invariants-end
        if ((len(result)) == (0)) or (((result)[(len(result)) - (1)]) != ((s)[i])):
            # assert-start
            Assert(Implies(len(result) > 0, result[len(result) - 1] < s[i]))
            Assert(Implies(len(result) > 0, 
                Forall(int, lambda j:
                    Implies(0 <= j and j < len(result), result[j] < s[i]))))
            # assert-end
            result = (result) + [(s)[i]]
        i = (i) + (1)
    return result
    # impl-end

def unique(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda k:
        (Implies(((0) <= (k)) and ((k) < (len(Result()))), InArray(s, Result()[k])))))
    Ensures(Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((0) <= (i)) and ((i) < (j))) and ((j) < (len(Result())))) or (((Result())[i]) < ((Result())[j])))))
    # post-conditions-end

    # impl-start
    a = BubbleSort(s)
    # assert-start
    Assert(Forall(int, lambda k:
        (Implies(((0) <= (k)) and ((k) < (len(a))), InArray(s, a[k])))))
    # assert-end
    b = uniqueSorted(a)
    # assert-start
    Assert(Forall(int, lambda k:
        (Implies(((0) <= (k)) and ((k) < (len(a))), InArray(s, a[k])))))
    Assert(Forall(int, lambda k:
        (Implies(((0) <= (k)) and ((k) < (len(b))), InArray(a, b[k])))))
    Assert(Forall(int, lambda k:
        (Implies(((0) <= (k)) and ((k) < (len(b))), InArray(s, b[k])))))
    # assert-end
    return b
    # impl-end

def BubbleSort(a1 : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(a1), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a1), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(a1)) == (len(Result())))
    Ensures(Forall(int, lambda i:
        Forall(int, lambda j:
            Implies((((0) <= (i)) and ((i) < (j))) and ((j) < (len((Result())))), ((Result())[i]) <= ((Result())[j])))))
    Ensures(Forall(int, lambda k:
        (Implies(((0) <= (k)) and ((k) < (len(Result()))), InArray(a1, Result()[k])))))
    # post-conditions-end

    # impl-start
    a : List[int] = []
    i : int = int(0)
    while i < len(a1):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(Acc(list_pred(a1), 1/2))
        Invariant(len(a) == i)
        Invariant(0 <= i and i <= len(a1))
        Invariant(Forall(int, lambda k:
            (Implies(((0) <= (k)) and ((k) < (i)), a[k] == a1[k]))))
        Invariant(Forall(int, lambda k:
            (Implies(((0) <= (k)) and ((k) < (i)), InArray(a1, a[k])), [[InArray(a1, a[k])]])))
        Invariant(Forall(int, lambda k:
            (Implies(((0) <= (k)) and ((k) < (i)), InArray(a, a1[k])), [[InArray(a, a1[k])]])))
        # invariants-end
        a = a + [a1[i]]
        # assert-start
        Assert(InArray(a1, a[i]))
        # assert-end
        i = i + 1
    i = (len((a))) - (1)
    while (i) > (0):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(Acc(list_pred(a1), 1/2))
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
        Invariant(Forall(int, lambda k:
            (Implies(((0) <= (k)) and ((k) < (len(a))), InArray(a1, a[k])), [[InArray(a1, a[k])]])))
        # invariants-end
        j : int = 0
        while (j) < (i):
            # invariants-start
            Invariant(Acc(list_pred(a)))
            Invariant(Acc(list_pred(a1), 1/2))
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
            Invariant(Forall(int, lambda k:
                (Implies(((0) <= (k)) and ((k) < (len(a))), InArray(a1, a[k])), [[InArray(a1, a[k])]])))
            # invariants-end
            if ((a)[j]) > ((a)[(j) + (1)]):
                rhs0_ : int = (a)[(j) + (1)]
                (a)[(j) + (1)] = (a)[j]
                (a)[j] = rhs0_
            j = (j) + (1)
        i = (i) - (1)
    return a
    # impl-end
