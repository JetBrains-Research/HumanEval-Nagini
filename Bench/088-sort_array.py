from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def sort__array(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (len(s)))
    Ensures(not (((len(s)) > (0)) and ((((((s)[0]) + ((s)[(len(s)) - (1)])) % 2)) == (0))) or (Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((0) <= (i)) and ((i) < (j))) and ((j) < (len(Result())))) or (((Result())[i]) >= ((Result())[j]))))))
    Ensures(not (((len(s)) > (0)) and ((((((s)[0]) + ((s)[(len(s)) - (1)])) % 2)) != (0))) or (Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((0) <= (i)) and ((i) < (j))) and ((j) < (len(Result())))) or (((Result())[i]) <= ((Result())[j]))))))
    # post-conditions-end

    # impl-start
    sorted : List[int] = []
    if (len(s)) == (0):
        sorted = list([])
        return sorted
    elif (((((s)[0]) + ((s)[(len(s)) - (1)])) % 2)) == (0):
        # assert-start
        Assert(len(s) > 0)
        # assert-end
        t : List[int] = BubbleSort(s)
        # assert-start
        Assert(Forall(int, lambda i:
            Forall(int, lambda j:
                Implies((((0) <= (i)) and ((i) < (j))) and ((j) < (len((t)))), ((t)[i]) <= ((t)[j])))))    
        # assert-end
        sorted = reverse(t) 
        # assert-start
        Assert(Forall(int, lambda i:
            Forall(int, lambda j:
                Implies((((0) <= (i)) and ((i) < (j))) and ((j) < (len((sorted)))), ((sorted)[i]) >= ((sorted)[j])))))    
        Assert(((len(s)) > (0)) and ((((((s)[0]) + ((s)[(len(s)) - (1)])) % 2)) == (0)))
        # assert-end
        return sorted
    else:
        # assert-start
        Assert(len(s) > 0)
        # assert-end
        sorted = BubbleSort(s)
        # assert-start
        Assert(Forall(int, lambda i:
            Forall(int, lambda j:
                Implies((((0) <= (i)) and ((i) < (j))) and ((j) < (len((sorted)))), ((sorted)[i]) <= ((sorted)[j])))))    
        Assert(((len(s)) > (0)) and ((((((s)[0]) + ((s)[(len(s)) - (1)])) % 2)) != (0)))
        # assert-end
        return sorted
    # impl-end

def reverse(str : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(str), 1/2))
    Requires(Forall(int, lambda x: Forall(int, lambda y: not (((0) <= (x)) and ((x) < (y)) and ((y) < (len(str)))) or ((str)[x] <= (str)[y]))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(str), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda x: Forall(int, lambda y: not (((0) <= (x)) and ((x) < (y)) and ((y) < (len(Result())))) or ((Result())[x] >= (Result())[y]))))
    Ensures(str == Old(str))
    Ensures((len(Result())) == (len(str)))
    Ensures(Forall(int, lambda k:
        not (((0) <= (k)) and ((k) < (len(str)))) or (((Result())[k]) == ((str)[((len(str)) - (1)) - (k)]))))
    # post-conditions-end

    # impl-start
    rev : List[int] = []
    i : int = 0
    while (i) < (len(str)):
        # invariants-start
        Invariant(Acc(list_pred(str), 1/2))
        Invariant(Acc(list_pred(rev)))
        Invariant(Forall(int, lambda x: Forall(int, lambda y: not (((0) <= (x)) and ((x) < (y)) and ((y) < (len(str)))) or ((str)[x] <= (str)[y]))))
        Invariant(((i) >= (0)) and ((i) <= (len(str))))
        Invariant((len(rev)) == (i))
        Invariant(Forall(int, lambda k:
            not (((0) <= (k)) and ((k) < (i))) or (((rev)[k]) == ((str)[(len(str) - (1)) - (k)]))))
        Invariant(Forall(int, lambda x: Forall(int, lambda y: (not (((0) <= (x)) and ((x) < (len(rev))) and (0 <= y and (y) < (len(str) - i))) or ((str)[y] <= (rev)[x]), [[str[y] <= rev[x]]]))))
        Invariant(Forall(int, lambda x: Forall(int, lambda y: (not (((0) <= (x)) and ((x) < (y)) and ((y) < (len(rev)))) or ((rev)[x] >= (rev)[y]), [[rev[x] >= rev[y]]]))))
        # invariants-end
        rev = (rev) + [(str)[(len(str) - (i)) - (1)]]
        i = (i) + (1)
    return rev
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
    # post-conditions-end

    # impl-start
    a : List[int] = list(a1)
    i : int = (len((a))) - (1)
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
            # invariants-end
            if ((a)[j]) > ((a)[(j) + (1)]):
                rhs0_ : int = (a)[(j) + (1)]
                (a)[(j) + (1)] = (a)[j]
                (a)[j] = rhs0_
            j = (j) + (1)
        i = (i) - (1)
    return a
    # impl-end
