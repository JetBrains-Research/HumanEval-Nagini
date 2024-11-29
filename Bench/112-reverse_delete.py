from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure 
def InArray(a : List[int], x : int) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    # pre-conditions-end

    # pure-start
    return Exists(int, lambda d_0_i_:
        ((((0) <= (d_0_i_)) and ((d_0_i_) < (len((a)))) and ((a)[d_0_i_]) == (x))))
    # pure-end

@Pure 
def NotInArray(a : List[int], x : int) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    # pre-conditions-end

    # pure-start
    return Forall(int, lambda d_0_i_:
        (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len((a)))), ((a)[d_0_i_]) != (x))))
    # pure-end

@Pure 
def implArrays(chars : List[int], res : List[int], x : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(chars)))
    Requires(Acc(list_pred(res)))
    # pre-conditions-end

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
    Ensures(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(Result()[0])))) or (NotInArray(chars, (Result()[0])[d_0_i_]))))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(Result()[0])))) or (InArray(s, (Result()[0])[d_1_i_]))))
    Ensures(Forall(int, lambda d_6_j_:
        not ((((0) <= (d_6_j_)) and ((d_6_j_) < (len(s))))) or (implArrays(chars, Result()[0], (s)[d_6_j_]))))
    # post-conditions-end

    # impl-start
    res : List[int] = []
    d_3_i_ : int = 0
    while (d_3_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(res)))
        Invariant(Acc(list_pred(s)))
        Invariant(Acc(list_pred(chars)))
        Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= (len(s))))
        Invariant(Forall(int, lambda d_4_i_:
            (not (((0) <= (d_4_i_)) and ((d_4_i_) < (len(res)))) or (NotInArray(chars, (res)[d_4_i_])), [[]])))
        Invariant(Forall(int, lambda d_5_i_:
            (not (((0) <= (d_5_i_)) and ((d_5_i_) < (len(res)))) or (InArray(s, res[d_5_i_])), [[InArray(s, res[d_5_i_])]])))
        Invariant(Forall(int, lambda d_6_j_:
            (not ((((0) <= (d_6_j_)) and ((d_6_j_) < (d_3_i_)))) or (implArrays(chars, res, (s)[d_6_j_])), [[InArray(res, (s)[d_6_j_])]])))
        # invariants-end
        if NotInArray(chars, (s)[d_3_i_]):
            res = (res) + [(s)[d_3_i_]]
        d_3_i_ = (d_3_i_) + (1)
    is__palindrome : bool = is__palindrome__fun(res)
    return (res, is__palindrome)
    # impl-end

def is__palindrome__fun(text : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(text), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(text), 1/2))
    Ensures((Result()) == (Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(text)))) or (((text)[d_0_i_]) == ((text)[((len(text)) - (d_0_i_)) - (1)])))))
    Ensures(Result() == is__palindrome__pred(text))
    # post-conditions-end

    # impl-start
    result : bool = True
    d_1_i_ : int = 0
    while (d_1_i_) < ((len(text) // 2)):
        # invariant-start
        Invariant(Acc(list_pred(text), 1/2))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= ((len(text) // 2))))
        Invariant((result) == (Forall(int, lambda d_2_i1_:
            (not (((d_2_i1_) >= (0)) and ((d_2_i1_) < (d_1_i_))) or (((text)[d_2_i1_]) == ((text)[((len(text)) - (d_2_i1_)) - (1)])), [[]]))))
        # invariant-end
        if ((text)[d_1_i_]) != ((text)[((len(text)) - (d_1_i_)) - (1)]):
            result = False
        d_1_i_ = (d_1_i_) + (1)
    return result
    # impl-end

@Pure
def is__palindrome__pred(s : List[int]) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    # pre-conditions-end

    # pure-start
    return Forall(int, lambda d_10_k_:
        (not (((0) <= (d_10_k_)) and ((d_10_k_) < (len(s)))) or (((s)[d_10_k_]) == ((s)[((len(s)) - (1)) - (d_10_k_)]))))
    # pure-end
