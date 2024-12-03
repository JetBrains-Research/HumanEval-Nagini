from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def WithinRange(n : int) -> bool:
    # pure-start
    return ((n) >= (1)) and ((n) <= (9))
    # pure-end

@Pure 
def WithinRangeString(s : str) -> bool:
    # pure-start
    return (s == "One" or s == "Two" or s == "Three" or s == "Four" or s == "Five" or s == "Six" or s == "Seven" or s == "Eight" or s == "Nine")
    # pure-end

def SortReverseAndName(arr : List[int]) -> List[str]:
    # pre-conditions-start
    Requires(Acc(list_pred(arr)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(arr)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) <= (len(arr)))
    Ensures(Forall(int, lambda i:
        Implies(((0) <= (i)) and ((i) < (len(Result()))), 
            WithinRangeString(Result()[i]))))
    # post-conditions-end

    # impl-start
    validNumbers : List[int] = []
    i : int = int(0)
    while (i) < (len(arr)):
        # invariants-start
        Invariant(Acc(list_pred(validNumbers)))
        Invariant(Acc(list_pred(arr)))
        Invariant(((0) <= (i)) and ((i) <= (len(arr))))
        Invariant((len(validNumbers)) <= (i))
        Invariant(Forall(int, lambda j:
            (Implies(((0) <= (j)) and ((j) < (len(validNumbers))), WithinRange(validNumbers[j])), 
                [[]])))
        # invariants-end
        if WithinRange((arr)[i]):
            validNumbers = (validNumbers) + [(arr)[i]]
        i = (i) + (1)
    # assert-start
    Assert(len(validNumbers) <= len(arr))
    # assert-end
    validNumbers = BubbleSort(validNumbers)

    validNumbers = reverse(validNumbers)
    i = 0
    result : List[str] = []
    while (i) < (len(validNumbers)):
        # invariants-start
        Invariant(Acc(list_pred(validNumbers)))
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(arr)))
        Invariant(((0) <= (i)) and ((i) <= (len(validNumbers))))
        Invariant(len(validNumbers) <= len(arr))
        Invariant(i <= len(arr))
        Invariant((len(result)) == (i))
        Invariant(Forall(int, lambda j:
            (Implies(((0) <= (j)) and ((j) < (len(validNumbers))), ((1) <= ((validNumbers)[j])) and (((validNumbers)[j]) <= (9))), 
                [[(validNumbers)[j]]])))
        Invariant(Forall(int, lambda i:
            (Implies(((0) <= (i)) and ((i) < (len(result))), 
                WithinRangeString(result[i])), 
                [[]])))
        # invariants-end
        result = (result) + [NumberToName((validNumbers)[i])]
        i = (i) + (1)
    return result
    # impl-end

def BubbleSort(a1 : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(a1), 1/2))
    Requires(Forall(int, lambda j:
        Implies(((0) <= (j)) and ((j) < (len(a1))), ((1) <= ((a1)[j])) and (((a1)[j]) <= (9)))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a1), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda j:
        Implies(((0) <= (j)) and ((j) < (len(Result()))), ((1) <= ((Result())[j])) and (((Result())[j]) <= (9)))))
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
        Invariant(Forall(int, lambda j:
            (Implies(((0) <= (j)) and ((j) < (len(a))), ((1) <= ((a)[j])) and (((a)[j]) <= (9))), 
                [[(a)[j]]])))    
        Invariant((len(a1)) == (len(a)))
        Invariant(Implies((i) < (0), (len((a))) == (0)))
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
            Invariant(Forall(int, lambda j:
                (Implies(((0) <= (j)) and ((j) < (len(a))), ((1) <= ((a)[j])) and (((a)[j]) <= (9))), 
                    [[(a)[j]]])))    
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

def reverse(str : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(str), 1/2))
    Requires(Forall(int, lambda x: Forall(int, lambda y: Implies(((0) <= (x)) and ((x) < (y)) and ((y) < (len(str))), (str)[x] <= (str)[y]))))
    Requires(Forall(int, lambda j:
        Implies(((0) <= (j)) and ((j) < (len(str))), ((1) <= ((str)[j])) and (((str)[j]) <= (9))))) 
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(str), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda j:
        Implies(((0) <= (j)) and ((j) < (len(str))), ((1) <= ((str)[j])) and (((str)[j]) <= (9))))) 
    Ensures(Forall(int, lambda x: Forall(int, lambda y: Implies(((0) <= (x)) and ((x) < (y)) and ((y) < (len(Result()))), (Result())[x] >= (Result())[y]))))
    Ensures(str == Old(str))
    Ensures((len(Result())) == (len(str)))
    Ensures(Forall(int, lambda k:
        Implies(((0) <= (k)) and ((k) < (len(str))), ((Result())[k]) == ((str)[((len(str)) - (1)) - (k)]))))
    # post-conditions-end

    # impl-start
    rev : List[int] = []
    i : int = 0
    while (i) < (len(str)):
        # invariants-start
        Invariant(Acc(list_pred(str), 1/2))
        Invariant(Acc(list_pred(rev)))
        Invariant(Forall(int, lambda j:
            (Implies(((0) <= (j)) and ((j) < (len(str))), ((1) <= ((str)[j])) and (((str)[j]) <= (9))), [[str[j]]]))) 
        Invariant(Forall(int, lambda j:
            ( Implies(((0) <= (j)) and ((j) < (len(rev))), ((1) <= ((rev)[j])) and (((rev)[j]) <= (9))), [[rev[j]]]))) 
        Invariant(Forall(int, lambda x: 
            (Forall(int, lambda y: 
                    (Implies(((0) <= (x)) and ((x) < (y)) and ((y) < (len(str))), (str)[x] <= (str)[y]), [[str[y]]])), 
                [[str[x]]])))
        Invariant(((i) >= (0)) and ((i) <= (len(str))))
        Invariant((len(rev)) == (i))
        Invariant(Forall(int, lambda k:
            Implies(((0) <= (k)) and ((k) < (i)), ((rev)[k]) == ((str)[(len(str) - (1)) - (k)]))))
        Invariant(Forall(int, lambda x: 
            Forall(int, lambda y: 
                (Implies(((0) <= (x)) and ((x) < (len(rev))) and (0 <= y and (y) < (len(str) - i)), (str)[y] <= (rev)[x]), [[str[y] <= rev[x]]]))))
        Invariant(Forall(int, lambda x: 
            Forall(int, lambda y:
                (Implies(((0) <= (x)) and ((x) < (y)) and ((y) < (len(rev))), (rev)[x] >= (rev)[y]), [[rev[x] >= rev[y]]]))))
        # invariants-end 
        rev = (rev) + [(str)[(len(str) - (i)) - (1)]]
        i = (i) + (1)
    return rev
    # impl-end

def NumberToName(n : int) -> str :
    # pre-conditions-start
    Requires(n >= 1 and n <= 9)
    # pre-conditions-end
    # post-conditions-start
    Ensures(WithinRangeString(Result()))
    # pos-conditions-end

    # impl-start
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
    # impl-end
