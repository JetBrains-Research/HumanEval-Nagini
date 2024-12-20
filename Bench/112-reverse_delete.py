from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure 
def InArray(a : List[int], x : int) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(a)))
    # pure-pre-conditions-end

    # pure-start
    return Exists(int, lambda i:
        ((((0) <= (i)) and ((i) < (len((a)))) and ((a)[i]) == (x))))
    # pure-end

@Pure 
def NotInArray(a : List[int], x : int) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(a)))
    # pure-pre-conditions-end

    # pure-start
    return Forall(int, lambda i:
        (Implies(((0) <= (i)) and ((i) < (len((a)))), ((a)[i]) != (x))))
    # pure-end

@Pure 
def implArrays(chars : List[int], res : List[int], x : int) -> bool:
    # pure-pre-conditions-start
    Requires(Acc(list_pred(chars)))
    Requires(Acc(list_pred(res)))
    # pure-pre-conditions-end

    # pure-start
    return Implies(NotInArray(chars, x), InArray(res, x))
    # pure-end

def reverse__delete(s : List[int], chars : List[int]) -> Tuple[List[int], bool]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Acc(list_pred(chars)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result()[0])))
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(chars)))
    Ensures((Result()[1]) == (is__palindrome__pred(Result()[0])))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result()[0])))) or (NotInArray(chars, (Result()[0])[i]))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result()[0])))) or (InArray(s, (Result()[0])[i]))))
    Ensures(Forall(int, lambda j:
        not ((((0) <= (j)) and ((j) < (len(s))))) or (implArrays(chars, Result()[0], (s)[j]))))
    # post-conditions-end

    # impl-start
    res : List[int] = []
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(res)))
        Invariant(Acc(list_pred(s)))
        Invariant(Acc(list_pred(chars)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant(Forall(int, lambda i:
            (not (((0) <= (i)) and ((i) < (len(res)))) or (NotInArray(chars, (res)[i])), [[]])))
        Invariant(Forall(int, lambda i:
            (not (((0) <= (i)) and ((i) < (len(res)))) or (InArray(s, res[i])), [[InArray(s, res[i])]])))
        Invariant(Forall(int, lambda j:
            (not ((((0) <= (j)) and ((j) < (i)))) or (implArrays(chars, res, (s)[j])), [[InArray(res, (s)[j])]])))
        # invariants-end
        if NotInArray(chars, (s)[i]):
            res = (res) + [(s)[i]]
        i = (i) + (1)
    is__palindrome : bool = is__palindrome__fun(res)
    return (res, is__palindrome)
    # impl-end

def is__palindrome__fun(text : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(text), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(text), 1/2))
    Ensures((Result()) == (Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(text)))) or (((text)[i]) == ((text)[((len(text)) - (i)) - (1)])))))
    Ensures(Result() == is__palindrome__pred(text))
    # post-conditions-end

    # impl-start
    result : bool = True
    i : int = 0
    while (i) < ((len(text) // 2)):
        # invariant-start
        Invariant(Acc(list_pred(text), 1/2))
        Invariant(((0) <= (i)) and ((i) <= ((len(text) // 2))))
        Invariant((result) == (Forall(int, lambda i1:
            (not (((i1) >= (0)) and ((i1) < (i))) or (((text)[i1]) == ((text)[((len(text)) - (i1)) - (1)])), [[]]))))
        # invariant-end
        if ((text)[i]) != ((text)[((len(text)) - (i)) - (1)]):
            result = False
        i = (i) + (1)
    return result
    # impl-end

@Pure
def is__palindrome__pred(s : List[int]) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    # pure-pre-conditions-end

    # pure-start
    return Forall(int, lambda k:
        (not (((0) <= (k)) and ((k) < (len(s)))) or (((s)[k]) == ((s)[((len(s)) - (1)) - (k)]))))
    # pure-end
