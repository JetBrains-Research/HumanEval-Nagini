from typing import List
from nagini_contracts.contracts import *

def solve(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result()), 1/2))
    Ensures(Acc(list_pred(s), 1/2))
    Ensures((len(s)) == (len(Result())))
    Ensures(Implies(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (not(is__alpha((s)[i])))), Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((s)[i]) == ((Result())[((len(Result())) - (1)) - (i)])))))
    Ensures(Implies(Exists(int, lambda i:
        (((0) <= (i)) and ((i) < (len(s)))) and (is__alpha((s)[i]))), Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or ((((Result())[i]) == (flip__case((s)[i])) if is__alpha((s)[i]) else ((Result())[i]) == ((s)[i]))))))
    # post-conditions-end

    # impl-start
    t : List[int] = []
    flag : bool = False
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(t)))
        Invariant(Acc(list_pred(s), 1/2))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant((len(t)) == (i))
        Invariant(Implies(flag, Exists(int, lambda j:
            (((0) <= (j)) and ((j) < (i))) and (is__alpha((s)[j])))))
        Invariant(Implies(Exists(int, lambda j:
            (((0) <= (j)) and ((j) < (i))) and (is__alpha((s)[j]))), flag))
        Invariant(Implies(not(flag), Forall(int, lambda j:
            Implies(((0) <= (j)) and (j) < (i), not(is__alpha((s)[j]))))))
        Invariant(Implies(Forall(int, lambda j:
            Implies(((0) <= (j)) and (j) < (i), not(is__alpha((s)[j])))), not(flag)))
        Invariant(Forall(int, lambda j:
            (Implies(((0) <= (j)) and ((j) < (i)), ((t)[j]) == ((flip__case((s)[j]) if is__alpha((s)[j]) else (s)[j]))), [[]])))
        # invariants-end
        if is__alpha((s)[i]):
            t = (t) + [flip__case((s)[i])]
            flag = True
        else:
            t = (t) + [(s)[i]]
        i = (i) + (1)
    if not(flag):
        t = reverse(t)
    return t
    # impl-end

def reverse(str : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(str), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(str), 1/2))
    Ensures(Acc(list_pred(Result())))
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
        Invariant(((i) >= (0)) and ((i) <= (len(str))))
        Invariant((len(rev)) == (i))
        Invariant(Forall(int, lambda k:
            not (((0) <= (k)) and ((k) < (i))) or (((rev)[k]) == ((str)[(len(str) - (1)) - (k)]))))
        # invariants-end
        rev = (rev) + [(str)[(len(str) - (i)) - (1)]]
        i = (i) + (1)
    return rev
    # impl-end

@Pure
def is__alpha(c : int) -> bool :
    # pure-start
    return (((97) <= (c)) and ((c) <= (122))) or (((65) <= (c)) and ((c) <= (90)))
    # pure-end

@Pure
def flip__case(c : int) -> int :
    # pure-start
    if ((97) <= (c)) and ((c) <= (122)):
        return ((c) - (97)) + (65)
    elif True:
        return ((c) - (65)) + (97)
    # pure-end
