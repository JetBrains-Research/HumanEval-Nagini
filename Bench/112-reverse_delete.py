from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure 
def InArray(a : List[int], x : int) -> bool :
    Requires(Acc(list_pred(a)))
    return Exists(int, lambda d_0_i_:
        (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len((a)))), ((a)[d_0_i_]) == (x))))

@Pure 
def NotInArray(a : List[int], x : int) -> bool :
    Requires(Acc(list_pred(a)))
    return Forall(int, lambda d_0_i_:
        (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len((a)))), ((a)[d_0_i_]) != (x))))

@Pure 
def implArrays(chars : List[int], res : List[int], x : int) -> bool:
    Requires(Acc(list_pred(chars)))
    Requires(Acc(list_pred(res)))
    return Implies(NotInArray(chars, x), InArray(res, x))

def reverse__delete(s : List[int], chars : List[int]) -> Tuple[List[int], bool]:
    Requires(Acc(list_pred(s)))
    Requires(Acc(list_pred(chars)))
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
    res : List[int] = []
    is__palindrome = False # type : bool
    d_3_i_ = int(0) # type : int
    d_3_i_ = 0
    while (d_3_i_) < (len(s)):
        Invariant(Acc(list_pred(res)))
        Invariant(Acc(list_pred(s)))
        Invariant(Acc(list_pred(chars)))
        Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= (len(s))))
        Invariant(Forall(int, lambda d_4_i_:
            (not (((0) <= (d_4_i_)) and ((d_4_i_) < (len(res)))) or (NotInArray(chars, (res)[d_4_i_])), [[]])))
        Invariant(Forall(int, lambda d_5_i_:
            (not (((0) <= (d_5_i_)) and ((d_5_i_) < (len(res)))) or (InArray(s, res[d_5_i_])), [[InArray(s, res[d_5_i_])]])))
        Invariant(Forall(int, lambda d_6_j_:
            (not ((((0) <= (d_6_j_)) and ((d_6_j_) < (d_3_i_)))) or (implArrays(chars, res, (s)[d_6_j_])), [[implArrays(chars, res, (s)[d_6_j_])]])))
        if NotInArray(chars, (s)[d_3_i_]):
            res = (res) + [(s)[d_3_i_]]
        d_3_i_ = (d_3_i_) + (1)
    is__palindrome = is__palindrome__fun(res)
    Assert(Forall(int, lambda d_4_i_:
        (not (((0) <= (d_4_i_)) and ((d_4_i_) < (len(res)))) or (NotInArray(chars, (res)[d_4_i_])), [[NotInArray(chars, (res)[d_4_i_])]])))
    return (res, is__palindrome)

def is__palindrome__fun(text : List[int]) -> bool:
    Requires(Acc(list_pred(text), 1/2))
    Ensures(Acc(list_pred(text), 1/2))
    Ensures((Result()) == (Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(text)))) or (((text)[d_0_i_]) == ((text)[((len(text)) - (d_0_i_)) - (1)])))))
    Ensures(Result() == is__palindrome__pred(text))
    result = False # type : bool
    result = True
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < ((len(text) // 2)):
        Invariant(Acc(list_pred(text), 1/2))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= ((len(text) // 2))))
        Invariant((result) == (Forall(int, lambda d_2_i1_:
            (not (((d_2_i1_) >= (0)) and ((d_2_i1_) < (d_1_i_))) or (((text)[d_2_i1_]) == ((text)[((len(text)) - (d_2_i1_)) - (1)])), [[]]))))
        if ((text)[d_1_i_]) != ((text)[((len(text)) - (d_1_i_)) - (1)]):
            result = False
        d_1_i_ = (d_1_i_) + (1)
    return result

@Pure
def is__palindrome__pred(s : List[int]) -> bool :
    Requires(Acc(list_pred(s), 1/2))
    return Forall(int, lambda d_10_k_:
        (not (((0) <= (d_10_k_)) and ((d_10_k_) < (len(s)))) or (((s)[d_10_k_]) == ((s)[((len(s)) - (1)) - (d_10_k_)])), [[]]))

