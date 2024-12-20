from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def is__palindrome(start : int, s : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires((len(s)) > (0))
    Requires(((0) <= (start)) and ((start) < (len(s))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s), 1/2))
    Ensures(((0) <= (start)) and ((start) < (len(s))))
    Ensures((len(s)) > (0))
    Ensures((Result()) == (Forall(int, lambda k:
        not (((start) <= (k)) and ((k) < (len(s)))) or (((s)[k]) == ((s)[((len(s)) - (1)) - (k - start)])))))
    Ensures(Result() == is__palindrome__fun(start, s))
    # post-conditions-end

    # impl-start
    i : int = start
    j : int = (len(s)) - (1)
    while (i) < (j):
        # invariants-start
        Invariant(Acc(list_pred(s), 1/2))
        Invariant(((0) <= (start)) and ((start) < (len(s))))
        Invariant(i <= j + 1)
        Invariant(((start) <= (i)) and ((i) < (len(s))))
        Invariant(((start) <= (j)) and ((j) < (len(s))))
        Invariant((j - start) == (((len(s)) - (i)) - (1)))
        Invariant(Forall(int, lambda k:
            not (((start) <= (k)) and ((k) < (i))) or (((s)[k]) == ((s)[((len(s)) - (1)) - (k - start)]))))
        # invariants-end
        if ((s)[i]) != ((s)[j]):
            return False
        i = (i) + (1)
        j = (j) - (1)
    return True
    # impl-end

@Pure
def is__palindrome__fun(start : int, s : List[int]) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(0 <= start and start < len(s))
    # pure-pre-conditions-end

    # pure-start
    return Forall(int, lambda k:
        not (((start) <= (k)) and ((k) < (len(s)))) or (((s)[k]) == ((s)[((len(s)) - (1)) - (k - start)])))
    # pure-end

@Pure
def starts__with(result : List[int], s : List[int]) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(Acc(list_pred(result), 1/2))
    # pure-pre-conditions-end

    # pure-start
    return ((len(result)) >= (len(s))) and (Forall(int, lambda k:
        not (((0) <= (k)) and ((k) < (len(s)))) or (((result)[k]) == ((s)[k]))))
    # pure-end

def make__palindrome(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) <= ((2) * (len(s))))
    Ensures(len(Result()) == 0 or is__palindrome__fun(0, Result()))
    Ensures(starts__with(Result(), s))
    # post-conditions-end

    # impl-start
    result : List[int] = list([int(0)] * 0)
    if (len(s)) == (0):
        result = []
        return result
    beginning__of__suffix : int = int(0)
    flag : bool = is__palindrome(beginning__of__suffix, s)
    while not(flag):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(len(s) > 0)
        Invariant((((beginning__of__suffix) >= (0)) and (((beginning__of__suffix) + (1)) < (len(s)))) or ((flag) and (((beginning__of__suffix) >= (0)) and ((beginning__of__suffix) < (len(s))))))
        Invariant(Implies(flag, is__palindrome__fun(beginning__of__suffix, s)))
        # invariants-end
        beginning__of__suffix = (beginning__of__suffix) + (1)
        flag = is__palindrome(beginning__of__suffix, s)
    reversed : List[int] = reverse(beginning__of__suffix, s)
    result = (s) + (reversed)
    return result
    # impl-end

def reverse(end : int, str : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(str), 1/2))
    Requires(0 <= end and end < len(str))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(str), 1/2))
    Ensures(0 <= end and end < len(str))
    Ensures(Acc(list_pred(Result())))
    Ensures(str == Old(str))
    Ensures((len(Result())) == (end))
    Ensures(Forall(int, lambda k:
        not (((0) <= (k)) and ((k) < (end))) or (((Result())[k]) == ((str)[((end) - (1)) - (k)]))))
    # post-conditions-end

    # impl-start
    rev : List[int] = []
    i : int = 0
    while (i) < (end):
        # invariants-start
        Invariant(Acc(list_pred(str), 1/2))
        Invariant(Acc(list_pred(rev)))
        Invariant(0 <= end and end < len(str))
        Invariant(((i) >= (0)) and ((i) <= (end)))
        Invariant((len(rev)) == (i))
        Invariant(Forall(int, lambda k:
            not (((0) <= (k)) and ((k) < (i))) or (((rev)[k]) == ((str)[(end - (1)) - (k)]))))
        # invariants-end
        rev = (rev) + [(str)[(end - (i)) - (1)]]
        i = (i) + (1)
    return rev
    # impl-end
