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

@Pure
def HasNoEvenDigit(n : int) -> bool :
    # pure-pre-conditions-start
    Requires(((0) <= (n)))
    # pure-pre-conditions-end

    # pure-start
    return (n == 0 or (((((n % 10) % 2)) != (0)) and (HasNoEvenDigit((n // 10)))))
    # pure-end

def UniqueDigits(x : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(x), 1/2))
    Requires(Forall(int, lambda i: Implies(i >= 0 and i < len(x), (x[i] >= 0))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(x), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(len(Result()) <= len(x))
    Ensures(Forall(int, lambda i: Implies(i >= 0 and i < len(x), (x[i] >= 0))))
    Ensures(Forall(int, lambda i: Implies(i >= 0 and i < len(Result()), (Result()[i] >= 0))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or (HasNoEvenDigit((Result())[i]))))
    Ensures(Forall(int, lambda e:
        not (((e) >= 0 and e < len(x)) and (HasNoEvenDigit(x[e]))) or 
            (Exists(int, lambda j: 
                (j >= 0 and j < len(Result())) and Result()[j] == x[e]))))
    Ensures(Forall(int, lambda e:
        not ((e) >= 0 and e < len(Result())) or (InArray(x, Result()[e]))))
    Ensures(Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((0) <= (i)) and ((i) < (j))) and ((j) < (len(Result())))) or (((Result())[i]) <= ((Result())[j])))))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    i : int = 0
    
    while i < len(x):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(x), 1/2))
        Invariant(0 <= i and i <= len(x))
        Invariant(len(result) <= i)
        Invariant(Forall(int, lambda i: Implies(i >= 0 and i < len(x), (x[i] >= 0))))
        Invariant(Forall(int, lambda i: Implies(i >= 0 and i < len(result), (result[i] >= 0))))
        Invariant(Forall(int, lambda j:
            (Implies(((0) <= (j)) and ((j) < (len(result))), HasNoEvenDigit((result)[j])), [[HasNoEvenDigit((result)[j])]])))
        Invariant(Forall(int, lambda e:
            (Implies(((e) >= 0 and e < i) and (HasNoEvenDigit(x[e])), 
                Exists(int, lambda j: 
                    (j >= 0 and j < len(result)) and result[j] == x[e])), 
                [[(HasNoEvenDigit(x[e]))]])))
        Invariant(Forall(int, lambda e:
            (Implies((e) >= 0 and e < len(result), 
                InArray(x, result[e])), 
                [[InArray(x, result[e])]])))
        # invariants-end
        if HasNoEvenDigit((x)[i]):
            result = (result) + [(x)[i]]
        i = (i) + (1)
    while (i) < (len(result)):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(x), 1/2))
        Invariant(len(result) <= len(x))
        Invariant(((0) <= (i)) and ((i) <= (len(result))))
        Invariant(Forall(int, lambda i: 
            (Implies(i >= 0 and i < len(x), (x[i] >= 0)), [[x[i]]])))
        Invariant(Forall(int, lambda i: 
            (Implies(i >= 0 and i < len(result), (result[i] >= 0)), [[result[i]]])))
        Invariant(Forall(int, lambda j:
            (Implies(((0) <= (j)) and ((j) < (len(result))), HasNoEvenDigit((result)[j])), [[HasNoEvenDigit((result)[j])]])))
        Invariant(Forall(int, lambda e:
            (Implies(((e) >= 0 and e < len(x)) and (HasNoEvenDigit(x[e])), 
                Exists(int, lambda j: 
                    (j >= 0 and j < len(result)) and result[j] == x[e])), 
                [[(HasNoEvenDigit(x[e]))]])))
        Invariant(Forall(int, lambda e:
            (Implies((e) >= 0 and e < len(result), 
                InArray(x, result[e])), 
                [[InArray(x, result[e])]])))
        Invariant(Forall(int, lambda j:
            (Forall(int, lambda k:
                (not ((((0) <= (j)) and ((j) < (k))) and ((k) < (i))) or (((result)[j]) <= ((result)[k])), 
                 [[(result)[k]]])), 
                [[(result)[j]]])))
        Invariant(Forall(int, lambda j:
            (not ((((0) <= (j)) and ((j) < (i)))) or 
                (Forall(int, lambda k:
                    (not ((((i) <= (k)) and ((k) < (len(result))))) or 
                        (((result)[j]) <= ((result)[k])), 
                    [[result[k]]]))), 
                [[(result)[j]]])))
        # invariants-end
        minIndex : int = i
        j : int = (i) + (1)
        while (j) < (len(result)):
            # invariants-start
            Invariant(Acc(list_pred(result)))
            Invariant(Acc(list_pred(x), 1/2))    
            Invariant(len(result) <= len(x))
            Invariant(((0) <= (i)) and ((i) < (len(result))))
            Invariant(Forall(int, lambda i: 
                (Implies(i >= 0 and i < len(x), (x[i] >= 0)), [[x[i]]])))
            Invariant(Forall(int, lambda i: 
                (Implies(i >= 0 and i < len(result), (result[i] >= 0)), [[result[i]]])))
            Invariant((((i) <= (minIndex)) and ((minIndex) < (j))) and ((j) <= (len(result))))
            Invariant(Forall(int, lambda j:
                (Implies(((0) <= (j)) and ((j) < (len(result))), HasNoEvenDigit((result)[j])), [[HasNoEvenDigit((result)[j])]])))
            Invariant(HasNoEvenDigit((result)[minIndex]))
            Invariant(Forall(int, lambda e:
                (Implies(((e) >= 0 and e < len(x)) and (HasNoEvenDigit(x[e])), 
                    Exists(int, lambda j: 
                        (j >= 0 and j < len(result)) and result[j] == x[e])), 
                    [[(HasNoEvenDigit(x[e]))]])))
            Invariant(Forall(int, lambda e:
                (Implies((e) >= 0 and e < len(result), 
                    InArray(x, result[e])), 
                    [[InArray(x, result[e])]])))
            Invariant(Forall(int, lambda j:
                (Forall(int, lambda k:
                    (not ((((0) <= (j)) and ((j) < (k))) and ((k) < (i))) or (((result)[j]) <= ((result)[k])), 
                    [[(result)[k]]])), 
                [[(result)[j]]])))
            Invariant(Forall(int, lambda k:
                (not (((i) <= (k)) and ((k) < (j))) or (((result)[minIndex]) <= ((result)[k])), [[((result)[k])]])))
            Invariant(Forall(int, lambda j:
                (not ((((0) <= (j)) and ((j) < (i)))) or 
                    (Forall(int, lambda k:
                        (not ((((i) <= (k)) and ((k) < (len(result))))) or 
                            (((result)[j]) <= ((result)[k])), 
                        [[result[k]]]))), 
                    [[(result)[j]]])))
            # invariants-end
            if ((result)[j]) < ((result)[minIndex]):
                minIndex = j
            j = (j) + (1)
        if (minIndex) != (i):
            temp : int = (result)[i]
            # assert-start
            Assert(HasNoEvenDigit((result)[minIndex]))
            # assert-end
            result[i] = (result)[minIndex]
            # assert-start
            Assert(HasNoEvenDigit(temp))
            # assert-end
            result[minIndex] = temp
        i = (i) + (1)
    return result
    # impl-end
