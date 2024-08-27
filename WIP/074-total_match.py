from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *


# def TotalMatch(list1 : List[List[int]], list2 : List[List[int]]) -> List[List[int]]:
#     Requires(Acc(list_pred(list2)))
#     Requires(Acc(list_pred(list1)))
#     Requires(Forall(list1, lambda x: Acc(list_pred(x))))
#     Requires(Forall(list2, lambda x: Acc(list_pred(x))))
#     Ensures(Acc(list_pred(list2)))
#     Ensures(Acc(list_pred(list1)))
#     Ensures(Forall(list1, lambda x: Acc(list_pred(x))))
#     Ensures(Forall(list2, lambda x: Acc(list_pred(x))))
#     Ensures(Acc(list_pred(Result())))
#     Ensures(Forall(int, lambda x: Implies(x >= 0 and x < len(Result()), Acc(list_pred(Result()[x])))))
#     Ensures(((len(Result())) == (len(list1))) or ((len(Result())) == (len(list2))))
#     # Ensures(((Result()) == (list1)) or ((Result()) == (list2)))
#     Ensures((sum__chars__rec(0, len(Result()), Result())) <= (sum__chars__rec(0, len(list1), list1)))
#     Ensures((sum__chars__rec(0, len(Result()), Result())) <= (sum__chars__rec(0, len(list2), list2)))
#     Ensures(not ((sum__chars__rec(0, len(list1), list1)) == (sum__chars__rec(0, len(list2), list2))) or ((Result()) == (list1)))
#     d_0_sum1_ = SumChars(list1) # type : int
#     d_1_sum2_ = SumChars(list2) # type : int
#     if (d_0_sum1_) <= (d_1_sum2_):
#         # res = list(list1) # type : List[List[int]]
#         return list1
#     else:
#         # res = list(list2) # type : List[List[int]]
#         return list2

@Pure
def sum__chars__rec(i : int, j : int, lst : List[List[int]]) -> int :
    Requires(Acc(list_pred(lst), 1/2))
    Requires(Forall(lst, lambda x: Acc(list_pred(x), 1/2)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(lst))))
    if i == j:
        return 0
    else:
        return len((lst)[j - 1]) + sum__chars__rec(i, j - 1, lst)

def SumChars(lst : List[List[int]]) -> int:
    Requires(Acc(list_pred(lst)))
    Requires(Forall(lst, lambda x: Acc(list_pred(x))))
    Ensures(Acc(list_pred(lst)))
    Ensures(Forall(lst, lambda x: Acc(list_pred(x))))
    # Ensures((Result()) == (sum__chars__rec(0, len(lst), lst)))
    sum = int(0) # type : int
    sum = 0
    d_3_i_ = int(0) # type : int
    d_3_i_ = 0
    Assert(Forall(int, lambda d_0_i_: (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(lst))), sum__chars__rec(0, d_0_i_ + 1, lst) == (sum__chars__rec(0, d_0_i_, lst) + len(lst[d_0_i_]))), 
        [[sum__chars__rec(0, d_0_i_ + 1, lst)]])))
    while (d_3_i_) < (len(lst)):
        Invariant(Acc(list_pred(lst), 1/2))
        Invariant(Forall(lst, lambda x: Acc(list_pred(x), 1/2)))
        Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= (len(lst))))
        Invariant(lst == Old(lst))
        # Invariant((sum) == (sum__chars__rec(0, d_3_i_, lst)))
        Assert(Forall(int, lambda d_0_i_: (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(lst))), sum__chars__rec(0, d_0_i_ + 1, lst) == (sum__chars__rec(0, d_0_i_, lst) + len(lst[d_0_i_]))), 
            [[sum__chars__rec(0, d_0_i_ + 1, lst)]])))
        Assert(sum__chars__rec(0, d_3_i_ + 1, lst) == sum__chars__rec(0, d_3_i_, lst) + len(lst[d_3_i_]))
        sum = (sum) + (len((lst)[d_3_i_]))
        d_3_i_ = (d_3_i_) + (1)
    return sum
