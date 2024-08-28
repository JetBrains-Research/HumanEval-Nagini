from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def WithinRange(n : int) -> bool:
    return ((n) >= (1)) and ((n) <= (9))

@Pure 
def WithinRangeString(s : str) -> bool:
    return (s == "One" or s == "Two" or s == "Three" or s == "Four" or s == "Five" or s == "Six" or s == "Seven" or s == "Eight" or s == "Nine")

def SortReverseAndName(arr : List[int]) -> List[str]:
    Requires(Acc(list_pred(arr)))
    Ensures(Acc(list_pred(arr)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) <= (len(arr)))
    Ensures(Forall(int, lambda d_0_i_:
        Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(Result()))), 
            WithinRangeString(Result()[d_0_i_]))))
    d_1_validNumbers_ : List[int] = [] # type : List[int]
    d_2_i_ = int(0) # type : int
    while (d_2_i_) < (len(arr)):
        Invariant(Acc(list_pred(d_1_validNumbers_)))
        Invariant(Acc(list_pred(arr)))
        Invariant(((0) <= (d_2_i_)) and ((d_2_i_) <= (len(arr))))
        Invariant((len(d_1_validNumbers_)) <= (d_2_i_))
        Invariant(Forall(int, lambda d_3_j_:
            (Implies(((0) <= (d_3_j_)) and ((d_3_j_) < (len(d_1_validNumbers_))), WithinRange(d_1_validNumbers_[d_3_j_])), 
                [[]])))
        if WithinRange((arr)[d_2_i_]):
            d_1_validNumbers_ = (d_1_validNumbers_) + [(arr)[d_2_i_]]
        d_2_i_ = (d_2_i_) + (1)
    Assert(len(d_1_validNumbers_) <= len(arr))
    d_1_validNumbers_ = BubbleSort(d_1_validNumbers_)

    d_1_validNumbers_ = reverse(d_1_validNumbers_)
    d_2_i_ = 0
    result : List[str] = [] # type : List[str]
    while (d_2_i_) < (len(d_1_validNumbers_)):
        Invariant(Acc(list_pred(d_1_validNumbers_)))
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(arr)))
        Invariant(((0) <= (d_2_i_)) and ((d_2_i_) <= (len(d_1_validNumbers_))))
        Invariant(len(d_1_validNumbers_) <= len(arr))
        Invariant(d_2_i_ <= len(arr))
        Invariant((len(result)) == (d_2_i_))
        Invariant(Forall(int, lambda d_9_j_:
            (Implies(((0) <= (d_9_j_)) and ((d_9_j_) < (len(d_1_validNumbers_))), ((1) <= ((d_1_validNumbers_)[d_9_j_])) and (((d_1_validNumbers_)[d_9_j_]) <= (9))), 
                [[(d_1_validNumbers_)[d_9_j_]]])))
        Invariant(Forall(int, lambda d_0_i_:
            (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(result))), 
                WithinRangeString(result[d_0_i_])), 
                [[]])))
        result = (result) + [NumberToName((d_1_validNumbers_)[d_2_i_])]
        d_2_i_ = (d_2_i_) + (1)
    return result

def BubbleSort(a1 : List[int]) -> List[int]:
    Requires(Acc(list_pred(a1), 1/2))
    Requires(Forall(int, lambda d_4_j_:
        Implies(((0) <= (d_4_j_)) and ((d_4_j_) < (len(a1))), ((1) <= ((a1)[d_4_j_])) and (((a1)[d_4_j_]) <= (9)))))
    Ensures(Acc(list_pred(a1), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_4_j_:
        Implies(((0) <= (d_4_j_)) and ((d_4_j_) < (len(Result()))), ((1) <= ((Result())[d_4_j_])) and (((Result())[d_4_j_]) <= (9)))))
    Ensures((len(a1)) == (len(Result())))
    Ensures(Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            Implies((((0) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (len((Result())))), ((Result())[d_0_i_]) <= ((Result())[d_1_j_])))))
    a = list(a1) # type : List[int]
    d_2_i_ = int(0) # type : int
    d_2_i_ = (len((a))) - (1)
    while (d_2_i_) > (0):
        Invariant(Acc(list_pred(a)))
        Invariant(Acc(list_pred(a1), 1/2))
        Invariant(Forall(int, lambda d_4_j_:
            (Implies(((0) <= (d_4_j_)) and ((d_4_j_) < (len(a))), ((1) <= ((a)[d_4_j_])) and (((a)[d_4_j_]) <= (9))), 
                [[(a)[d_4_j_]]])))    
        Invariant((len(a1)) == (len(a)))
        Invariant(Implies((d_2_i_) < (0), (len((a))) == (0)))
        Invariant(((-1) <= (d_2_i_)) and ((d_2_i_) < (len((a)))))
        Invariant(Forall(int, lambda d_3_ii_:
            (Forall(int, lambda d_4_jj_:
                (Implies((((d_2_i_) <= (d_3_ii_)) and ((d_3_ii_) < (d_4_jj_))) and ((d_4_jj_) < (len((a)))), ((a)[d_3_ii_]) <= ((a)[d_4_jj_])),
                    [[(a)[d_4_jj_]]])),
                [[(a)[d_3_ii_]]])))
        Invariant(Forall(int, lambda d_5_k_:
            (Forall(int, lambda d_6_k_k_:
                (Implies(((((0) <= (d_5_k_)) and ((d_5_k_) <= (d_2_i_))) and ((d_2_i_) < (d_6_k_k_)) and (d_6_k_k_) < (len((a)))), ((a)[d_5_k_]) <= ((a)[d_6_k_k_])),
                    [[(a)[d_6_k_k_]]])),
                [[(a)[d_5_k_]]])))
        d_7_j_ = int(0) # type : int
        d_7_j_ = 0
        while (d_7_j_) < (d_2_i_):
            Invariant(Acc(list_pred(a)))
            Invariant(Acc(list_pred(a1), 1/2))
            Invariant(Forall(int, lambda d_4_j_:
                (Implies(((0) <= (d_4_j_)) and ((d_4_j_) < (len(a))), ((1) <= ((a)[d_4_j_])) and (((a)[d_4_j_]) <= (9))), 
                    [[(a)[d_4_j_]]])))    
            Invariant((len(a1)) == (len(a)))
            Invariant((((0) < (d_2_i_)) and ((d_2_i_) < (len((a))))) and (((0) <= (d_7_j_)) and ((d_7_j_) <= (d_2_i_))))
            Invariant(Forall(int, lambda d_8_ii_:
                (Forall(int, lambda d_9_jj_:
                    (Implies((((d_2_i_) <= (d_8_ii_)) and ((d_8_ii_) <= (d_9_jj_))) and ((d_9_jj_) < (len((a)))), ((a)[d_8_ii_]) <= ((a)[d_9_jj_])),
                        [[(a)[d_9_jj_]]])),
                    [[(a)[d_8_ii_]]])))
            Invariant(Forall(int, lambda d_10_k_:
                (Forall(int, lambda d_11_k_k_:
                    (Implies(((((0) <= (d_10_k_)) and ((d_10_k_) <= (d_2_i_))) and ((d_2_i_) < (d_11_k_k_))) and ((d_11_k_k_) < (len((a)))), ((a)[d_10_k_]) <= ((a)[d_11_k_k_])),
                        [[(a)[d_11_k_k_]]])),
                    [[(a)[d_10_k_]]])))
            Invariant(Forall(int, lambda d_12_k_:
                (Implies(((0) <= (d_12_k_)) and ((d_12_k_) <= (d_7_j_)), ((a)[d_12_k_]) <= ((a)[d_7_j_])),
                    [[(a)[d_12_k_]]])))
            if ((a)[d_7_j_]) > ((a)[(d_7_j_) + (1)]):
                rhs0_ = (a)[(d_7_j_) + (1)] # type : int
                (a)[(d_7_j_) + (1)] = (a)[d_7_j_]
                (a)[d_7_j_] = rhs0_
            d_7_j_ = (d_7_j_) + (1)
        d_2_i_ = (d_2_i_) - (1)
    return a

def reverse(str : List[int]) -> List[int]:
    Requires(Acc(list_pred(str), 1/2))
    Requires(Forall(int, lambda x: Forall(int, lambda y: Implies(((0) <= (x)) and ((x) < (y)) and ((y) < (len(str))), (str)[x] <= (str)[y]))))
    Requires(Forall(int, lambda d_4_j_:
        Implies(((0) <= (d_4_j_)) and ((d_4_j_) < (len(str))), ((1) <= ((str)[d_4_j_])) and (((str)[d_4_j_]) <= (9))))) 
    Ensures(Acc(list_pred(str), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_4_j_:
        Implies(((0) <= (d_4_j_)) and ((d_4_j_) < (len(str))), ((1) <= ((str)[d_4_j_])) and (((str)[d_4_j_]) <= (9))))) 
    Ensures(Forall(int, lambda x: Forall(int, lambda y: Implies(((0) <= (x)) and ((x) < (y)) and ((y) < (len(Result()))), (Result())[x] >= (Result())[y]))))
    Ensures(str == Old(str))
    Ensures((len(Result())) == (len(str)))
    Ensures(Forall(int, lambda d_11_k_:
        Implies(((0) <= (d_11_k_)) and ((d_11_k_) < (len(str))), ((Result())[d_11_k_]) == ((str)[((len(str)) - (1)) - (d_11_k_)]))))
    rev = list([int(0)] * 0) # type : List[int]
    rev = []
    d_12_i_ = int(0) # type : int
    d_12_i_ = 0
    while (d_12_i_) < (len(str)):
        Invariant(Acc(list_pred(str), 1/2))
        Invariant(Acc(list_pred(rev)))
        Invariant(Forall(int, lambda d_4_j_:
            (Implies(((0) <= (d_4_j_)) and ((d_4_j_) < (len(str))), ((1) <= ((str)[d_4_j_])) and (((str)[d_4_j_]) <= (9))), [[str[d_4_j_]]]))) 
        Invariant(Forall(int, lambda d_4_j_:
            ( Implies(((0) <= (d_4_j_)) and ((d_4_j_) < (len(rev))), ((1) <= ((rev)[d_4_j_])) and (((rev)[d_4_j_]) <= (9))), [[rev[d_4_j_]]]))) 
        Invariant(Forall(int, lambda x: 
            (Forall(int, lambda y: 
                    (Implies(((0) <= (x)) and ((x) < (y)) and ((y) < (len(str))), (str)[x] <= (str)[y]), [[str[y]]])), 
                [[str[x]]])))
        Invariant(((d_12_i_) >= (0)) and ((d_12_i_) <= (len(str))))
        Invariant((len(rev)) == (d_12_i_))
        Invariant(Forall(int, lambda d_13_k_:
            Implies(((0) <= (d_13_k_)) and ((d_13_k_) < (d_12_i_)), ((rev)[d_13_k_]) == ((str)[(len(str) - (1)) - (d_13_k_)]))))
        Invariant(Forall(int, lambda x: 
            Forall(int, lambda y: 
                (Implies(((0) <= (x)) and ((x) < (len(rev))) and (0 <= y and (y) < (len(str) - d_12_i_)), (str)[y] <= (rev)[x]), [[str[y] <= rev[x]]]))))
        Invariant(Forall(int, lambda x: 
            Forall(int, lambda y:
                (Implies(((0) <= (x)) and ((x) < (y)) and ((y) < (len(rev))), (rev)[x] >= (rev)[y]), [[rev[x] >= rev[y]]]))))
        rev = (rev) + [(str)[(len(str) - (d_12_i_)) - (1)]]
        d_12_i_ = (d_12_i_) + (1)
    return rev

def NumberToName(n : int) -> str :
    Requires(n >= 1 and n <= 9)
    Ensures(WithinRangeString(Result()))
    if (n) == (1):
        return "One"

    if (n) == (2):
        return "Two"

    if (n) == (3):
        return "Three"

    if (n) == (4):
        return "Four"
    
    if (n) == (5):
        return "Five"

    if (n) == (6):
        return "Six"

    if (n) == (7):
        return "Seven"

    if (n) == (8):
        return "Eight"

    if (n) == (9):
        return "Nine"