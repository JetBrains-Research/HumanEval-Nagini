from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def IsValidParentheses(s : List[int], i : int, depth : int) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(i >= 0 and i <= len(s))
    # pure-pre-conditions-end

    # pure-start
    if (i) == (len(s)):
        return (depth) >= (0)
    elif (depth) < (0):
        return False
    elif ((s)[i]) == (0):
        return IsValidParentheses(s, (i) + (1), (depth) + (1))
    elif ((s)[i]) == (1):
        return ((depth) > (0)) and (IsValidParentheses(s, (i) + (1), (depth) - (1)))
    elif True:
        return IsValidParentheses(s, (i) + (1), depth)
    # pure-end

@Pure
def IsValidParentheses2(s : List[int], i : int, depth : int) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(i >= 0 and i <= len(s))
    # pure-pre-conditions-end

    # pure-start
    if (i) == (len(s)):
        return (depth) >= (0)
    elif (depth) < (0):
        return False
    elif ((s)[i]) == (0):
        return IsValidParentheses(s, (i) + (1), (depth) + (1))
    elif ((s)[i]) == (1):
        return ((depth) > (0)) and (IsValidParentheses(s, (i) + (1), (depth) - (1)))
    elif True:
        return IsValidParentheses(s, (i) + (1), depth)
    # pure-end

@Pure
def IsValidParentheses1(s : List[int], i : int, depth : int) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(i >= 0 and i <= len(s))
    # pure-pre-conditions-end

    # pure-start
    if (i) == (len(s)):
        return (depth) == (0)
    elif ((depth) <= (0)) and ((i) != (0)):
        return False
    elif ((s)[i]) == (0):
        return IsValidParentheses1(s, (i) + (1), (depth) + (1))
    elif ((s)[i]) == (1):
        return ((depth) > (0)) and (IsValidParentheses1(s, (i) + (1), (depth) - (1)))
    elif True:
        return IsValidParentheses1(s, (i) + (1), depth)
    # pure-end

def separate__paren__groups(paren__string : List[int]) -> List[List[int]]:
    # pre-conditions-start
    Requires(Acc(list_pred(paren__string)))
    Requires(Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(paren__string)))) or ((((paren__string)[i]) == (0)) or (((paren__string)[i]) == (1)))))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) <= (len(paren__string)))) or (IsValidParentheses(paren__string, i, 0))))
    Requires(IsValidParentheses2(paren__string, 0, 0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(ResultT(List[List[int]]))))
    Ensures(Forall(ResultT(List[List[int]]), lambda x: Acc(list_pred(x), 1/2)))
    Ensures((Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or (IsValidParentheses1((Result())[i], 0, 0)))))
    # post-conditions-end

    # impl-start
    res : List[List[int]] = []
    current__string : List[int] = []
    current__depth : int = int(0)
    i : int = int(0)
    while (i) < (len(paren__string)):
        # invariants-start
        Invariant(Acc(list_pred(res)))
        Invariant(Acc(list_pred(current__string)))
        Invariant(Acc(list_pred(paren__string)))
        Invariant(Forall(res, lambda i: Acc(list_pred(i), 1/2)))
        Invariant(((0) <= (i)) and ((i) <= (len(paren__string))))
        Invariant(Forall(int, lambda i:
            not (((i) >= (0)) and ((i) < (len(paren__string)))) or ((((paren__string)[i]) == (0)) or (((paren__string)[i]) == (1)))))
        Invariant(Forall(int, lambda i:
            not (((0) <= (i)) and ((i) <= (len(paren__string)))) or (IsValidParentheses(paren__string, i, 0))))
        Invariant((Forall(int, lambda i1:
            not (((0) <= (i1)) and ((i1) < (len(res)))) or (IsValidParentheses1((res)[i1], 0, 0)))))
        Invariant(IsValidParentheses(paren__string, i, 0))
        # invariants-end
        c = (paren__string)[i]
        if (c) == (0):
            current__depth = (current__depth) + (1)
            current__string = (current__string) + [c]
        elif (c) == (1):
            current__depth = (current__depth) - (1)
            current__string = (current__string) + [c]
            if (current__depth) == (0):
                res = (res) + [current__string]
                current__string = []
        i = (i) + (1)
    return res
    # impl-end

