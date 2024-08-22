from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def remove__duplicates(a : List[int]) -> List[int]:
    Requires(Acc(list_pred(a), 1/2))
    # Requires(Forall(int, lambda d_0_i_:
    #     not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(a)))) or ((count__rec(a, (a)[d_0_i_], len(a))) >= (1))))
    Ensures(Acc(list_pred(a), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(len(a) == len(Old(a)))
    Ensures(len(a) >= len(Result()))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(Result())))) or ((count__rec(a, (Result())[d_1_i_], len((Result())))) == (1))))
    # Ensures(Forall(int, lambda d_2_i_:
    #     not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(a)))) or ((((a)[d_2_i_]) in (Result())) == ((count__rec(a, (a)[d_2_i_], len(a))) == (1)))))
    result = list([int(0)] * 0) # type : List[int]
    result = []
    d_4_i_ = int(0) # type : int
    d_4_i_ = 0
    a_old = list(a)

    # if (len(a) > 0):
    #     d_8_cnt_ = int(0) # type : int
    #     var = (a)[d_4_i_] # type : int
    #     Assert(len((a)) == l1)
    #     b = list(a)
    #     d_8_cnt_ = count_my(a, var)
    #     Assert(len((a)) == l1)
    #     Assert(len(a) == len(b))
    #     Assert(count__rec(a, var, len(a)) == d_8_cnt_)
    #     Assert(len(Old(a)) == l1)
    while (d_4_i_) < (len(a)):
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(a), 1/2))
        Invariant(Acc(list_pred(a_old), 1/2))
        Invariant(len(a) == len(a_old))
        Invariant(Forall(int, lambda d_3_i_: (Implies(d_3_i_ >= 0 and d_3_i_ < len(a), a_old[d_3_i_] == a[d_3_i_]))))
        Invariant(((0) <= (d_4_i_)) and ((d_4_i_) <= (len(a))))
        Invariant(len(result) <= d_4_i_)
        Invariant(Forall(int, lambda d_5_j_:
            (Implies(((0) <= (d_5_j_)) and ((d_5_j_) < (len(result))), (count__rec(a, (result)[d_5_j_], len(a))) == (1)), [[count__rec(a, (result)[d_5_j_], len(a))]])))
        # Invariant(Forall(int, lambda d_6_j_:
        #     (Implies(((0) <= (d_6_j_)) and ((d_6_j_) < (d_4_i_)), (((a)[d_6_j_]) in (d_3_res_)) == ((count__rec(a, (a)[d_6_j_], len(a))) == (1))), [[count__rec(a, (a)[d_6_j_], len(a))]])))
        # Invariant(Forall(int, lambda d_7_j_:
        #     not (((0) <= (d_7_j_)) and ((d_7_j_) < (len(d_3_res_)))) or (((d_3_res_)[d_7_j_]) in (list((a)[:d_4_i_:])))))
        d_8_cnt_ = int(0) # type : int
        d_8_cnt_ = count_my(a, (a)[d_4_i_])
        if (d_8_cnt_) == (1):
            Assert(d_4_i_ < len(a_old))
            Assert(len(a) == len(a_old))
            Assert(count__rec(a, (a)[d_4_i_], len(a)) == 1)
            result = (result) + [(a)[d_4_i_]]
        d_4_i_ = (d_4_i_) + (1)
    return result

@Pure
def count__rec(a : List[int], x : int, i : int) -> int :
    Requires(Acc(list_pred(a), 1/2))
    Requires(((0) <= (i)) and ((i) <= (len(a))))
    if (i) == 0:
        return 0
    else:
        return (((a)[i - 1]) == (x)) + (count__rec(a, x, (i) - (1)))

def count_my(a : List[int], x : int) -> int:
    Requires(Acc(list_pred(a), 1/2))
    Ensures(Acc(list_pred(a), 1/2))
    Ensures(a == Old(a))
    Ensures((Result()) == (count__rec(a, x, len(a))))
    cnt = int(0) # type : int
    cnt = 0
    d_11_i_ = int(0) # type : int
    d_11_i_ = 0
    while (d_11_i_) < (len(a)):
        Invariant(Acc(list_pred(a), 1/2))
        Invariant(((0) <= (d_11_i_)) and ((d_11_i_) <= (len(a))))
        Invariant(Forall(int, lambda y: (Implies(y >= 0 and y < len(a), count__rec(a, x, y + 1) == (count__rec(a, x, y) + ((a)[y] == x))), [[count__rec(a, x, y + 1)]])))
        Invariant((cnt) == (count__rec(a, x, d_11_i_)))
        
        Assert(count__rec(a, x, d_11_i_ + 1) == (count__rec(a, x, d_11_i_) + ((a)[d_11_i_] == x)))
        if ((a)[d_11_i_]) == (x):
            cnt = (cnt) + (1)
        d_11_i_ = (d_11_i_) + (1)
    return cnt
