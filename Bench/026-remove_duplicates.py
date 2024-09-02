from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def remove__duplicates(a : List[int]) -> List[int]:
    Requires(Acc(list_pred(a), 1/2))
    Ensures(Acc(list_pred(a), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(len(a) == len(Old(a)))
    Ensures(len(a) >= len(Result()))
    Ensures(Forall(int, lambda d_2_i_:
        Implies(((0) <= (d_2_i_)) and ((d_2_i_) < (len(a))) and (count__rec(a, a[d_2_i_], len(a)) == 1), exists_check(Result(), a[d_2_i_]))))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(Result())))) or (count_check(a, (Result())[d_1_i_]))))
    result = list([int(0)] * 0) # type : List[int]
    result = []
    d_4_i_ = int(0) # type : int
    d_4_i_ = 0
    a_old = list(a)

    while (d_4_i_) < (len(a)):
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(a), 1/2))
        Invariant(Acc(list_pred(a_old), 1/2))
        Invariant(len(a) == len(a_old))
        Invariant(Forall(int, lambda d_3_i_: (Implies(d_3_i_ >= 0 and d_3_i_ < len(a), a_old[d_3_i_] == a[d_3_i_]))))
        Invariant(((0) <= (d_4_i_)) and ((d_4_i_) <= (len(a))))
        Invariant(len(result) <= d_4_i_)
        Invariant(Forall(int, lambda d_2_i_:
            (Implies(((0) <= (d_2_i_)) and ((d_2_i_) < (d_4_i_)) and (count__rec(a, a[d_2_i_], len(a)) == 1), exists_check(result, a[d_2_i_])), 
                [[]])))
        Invariant(Forall(int, lambda d_1_i_:
            (not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(result)))) or (count_check(a, (result)[d_1_i_])), 
                [[]])))
        d_8_cnt_ = int(0) # type : int
        d_8_cnt_ = count__rec(a, (a)[d_4_i_], len(a))
        if (d_8_cnt_) == (1):
            result = (result) + [(a)[d_4_i_]]
            Assert(count__rec(a, result[len(result) - 1], len(a)) == 1)
        d_4_i_ = (d_4_i_) + (1)
    return result

@Pure 
def exists_check(a : List[int], x : int) -> bool:
    Requires(Acc(list_pred(a), 1/2))
    return Exists(int, lambda d_0_i_:
        ((((0) <= (d_0_i_)) and ((d_0_i_) < (len((a)))) and ((a)[d_0_i_]) == (x))))

@Pure 
def count_check(a : List[int], x : int) -> bool:
    Requires(Acc(list_pred(a), 1/2))
    return (count__rec(a, x, len(a))) == (1)

@Pure
def count__rec(a : List[int], x : int, i : int) -> int :
    Requires(Acc(list_pred(a), 1/2))
    Requires(((0) <= (i)) and ((i) <= (len(a))))
    if (i) == 0:
        return 0
    else:
        return (((a)[i - 1]) == (x)) + (count__rec(a, x, (i) - (1)))
