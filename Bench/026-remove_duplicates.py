from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def remove__duplicates(a : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(len(a) == len(Old(a)))
    Ensures(len(a) >= len(Result()))
    Ensures(Forall(int, lambda d_2_i_:
        Implies(((0) <= (d_2_i_)) and ((d_2_i_) < (len(a))) and (count__rec(a, a[d_2_i_], len(a)) == 1), exists_check(Result(), a[d_2_i_]))))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(Result())))) or (count_check(a, (Result())[d_1_i_]))))
    # post-conditions-end

    # impl-start
    result = list([int(0)] * 0) # type : List[int]
    result = []
    d_4_i_ = int(0) # type : int
    d_4_i_ = 0
    a_old = list(a)

    while (d_4_i_) < (len(a)):
        # invariants-start
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
        # invariants-end
        d_8_cnt_ = int(0) # type : int
        d_8_cnt_ = count__rec(a, (a)[d_4_i_], len(a))
        if (d_8_cnt_) == (1):
            result = (result) + [(a)[d_4_i_]]
            # assert-start
            Assert(count__rec(a, result[len(result) - 1], len(a)) == 1)
            # assert-end
        d_4_i_ = (d_4_i_) + (1)
    return result
    # impl-end

@Pure 
def exists_check(a : List[int], x : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    # pre-conditions-end

    # impl-start
    return Exists(int, lambda d_0_i_:
        ((((0) <= (d_0_i_)) and ((d_0_i_) < (len((a)))) and ((a)[d_0_i_]) == (x))))
    # impl-end

@Pure 
def count_check(a : List[int], x : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    # pre-conditions-end

    # impl-start
    return (count__rec(a, x, len(a))) == (1)
    # impl-end

@Pure
def count__rec(a : List[int], x : int, i : int) -> int :
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    Requires(((0) <= (i)) and ((i) <= (len(a))))
    # pre-conditions-end

    # impl-start
    if (i) == 0:
        return 0
    else:
        return (((a)[i - 1]) == (x)) + (count__rec(a, x, (i) - (1)))
    # impl-end
