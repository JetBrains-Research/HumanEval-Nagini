from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def IsValidParentheses(s : List[int], i : int, depth : int) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(i >= 0 and i <= len(s))
    # pre-conditions-end

    # impl-start
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
    # impl-end

@Pure
def IsValidParentheses2(s : List[int], i : int, depth : int) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(i >= 0 and i <= len(s))
    # pre-conditions-end

    # impl-start
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
    # impl-end

@Pure
def IsValidParentheses1(s : List[int], i : int, depth : int) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(i >= 0 and i <= len(s))
    # pre-conditions-end

    # impl-start
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
    # impl-end

def separate__paren__groups(paren__string : List[int]) -> List[List[int]]:
    # pre-conditions-start
    Requires(Acc(list_pred(paren__string)))
    Requires(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(paren__string)))) or ((((paren__string)[d_0_i_]) == (0)) or (((paren__string)[d_0_i_]) == (1)))))
    Requires(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) <= (len(paren__string)))) or (IsValidParentheses(paren__string, d_1_i_, 0))))
    Requires(IsValidParentheses2(paren__string, 0, 0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(ResultT(List[List[int]]))))
    Ensures(Forall(ResultT(List[List[int]]), lambda x: Acc(list_pred(x), 1/2)))
    Ensures((Forall(int, lambda d_2_i_:
        not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(Result())))) or (IsValidParentheses1((Result())[d_2_i_], 0, 0)))))
    # post-conditions-end

    # impl-start
    res : List[List[int]] = []
    d_3_current__string_ : List[int] = []
    d_4_current__depth_ = int(0) # type : int
    d_5_i_ = int(0) # type : int
    while (d_5_i_) < (len(paren__string)):
        # invariants-start
        Invariant(Acc(list_pred(res)))
        Invariant(Acc(list_pred(d_3_current__string_)))
        Invariant(Acc(list_pred(paren__string)))
        Invariant(Forall(res, lambda d_4_i_: Acc(list_pred(d_4_i_), 1/2)))
        Invariant(((0) <= (d_5_i_)) and ((d_5_i_) <= (len(paren__string))))
        Invariant(Forall(int, lambda d_0_i_:
            not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(paren__string)))) or ((((paren__string)[d_0_i_]) == (0)) or (((paren__string)[d_0_i_]) == (1)))))
        Invariant(Forall(int, lambda d_1_i_:
            not (((0) <= (d_1_i_)) and ((d_1_i_) <= (len(paren__string)))) or (IsValidParentheses(paren__string, d_1_i_, 0))))
        Invariant((Forall(int, lambda d_6_i1_:
            not (((0) <= (d_6_i1_)) and ((d_6_i1_) < (len(res)))) or (IsValidParentheses1((res)[d_6_i1_], 0, 0)))))
        Invariant(IsValidParentheses(paren__string, d_5_i_, 0))
        # invariants-end
        d_7_c_ = (paren__string)[d_5_i_]
        if (d_7_c_) == (0):
            d_4_current__depth_ = (d_4_current__depth_) + (1)
            d_3_current__string_ = (d_3_current__string_) + [d_7_c_]
        elif (d_7_c_) == (1):
            d_4_current__depth_ = (d_4_current__depth_) - (1)
            d_3_current__string_ = (d_3_current__string_) + [d_7_c_]
            if (d_4_current__depth_) == (0):
                res = (res) + [d_3_current__string_]
                d_3_current__string_ = []
        d_5_i_ = (d_5_i_) + (1)
    return res
    # impl-end

