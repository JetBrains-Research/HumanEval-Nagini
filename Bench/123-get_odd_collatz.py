from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def iterate__to__odd(n : int) -> int :
    Requires(n % 2 == 0)
    Requires(n >= 0)
    Ensures(Result() % 2 == 1)
    Ensures(Result() > 0)
    if (n // 2) % 2 == 1:
        return n // 2
    else:
        return iterate__to__odd(n // 2)

@Pure
def next__odd__collatz(n : int) -> int :
    Requires(n > 0)
    Ensures(Result() > 0)
    Ensures(Result() % 2 == 1)
    if ((n % 2)) == (0):
        return iterate__to__odd(n)
    else:
        return iterate__to__odd(((3) * (n)) + (1))


def next__odd__collatz__iter(n : int) -> int:
    Requires((n) > (0))
    Ensures(Result() > 0)
    Ensures(((Result() % 2)) == (1))
    Ensures((Result()) == (next__odd__collatz(n)))
    next = int(0) # type : int
    next = n
    if ((next % 2)) == (1):
        next = ((3) * (next)) + (1)
    d_0_start_ = next # type : int
    while ((next % 2)) == (0):
        Invariant((next) > (0))
        Invariant(not (((next % 2)) == (0)) or ((next__odd__collatz(next)) == (next__odd__collatz(n))))
        Invariant(not (((next % 2)) == (0)) or ((iterate__to__odd(next)) == (iterate__to__odd(d_0_start_))))
        Invariant(not (((next % 2)) == (1)) or ((next) == (iterate__to__odd(d_0_start_))))
        next = (next // 2)
    return next


def get__odd__collatz__unsorted(n : int) -> List[int]:
    Requires((n) > (1))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(Result())))) or ((((Result())[d_1_i_] > 0)))))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(Result())))) or ((((Result())[d_1_i_] % 2)) == (1))))
    Ensures(Forall(int, lambda d_2_i_:
        not (((1) <= (d_2_i_)) and ((d_2_i_) < (len(Result())))) or (((Result())[d_2_i_]) == (next__odd__collatz((Result())[(d_2_i_) - (1)])))))
    odd__collatz = list([int(0)] * 0) # type : List[int]
    d_3_cur_ = int(0) # type : int
    d_3_cur_ = n
    if ((d_3_cur_ % 2)) == (0):
        d_3_cur_ = next__odd__collatz__iter(d_3_cur_)
    odd__collatz = [d_3_cur_]
    Assert(len(odd__collatz) == 1)
    Assert(Forall(int, lambda d_5_i_:
        (not (((1) <= (d_5_i_)) and ((d_5_i_) < (len(odd__collatz)))))))
    Assert(Forall(int, lambda d_5_i_:
        (not (((1) <= (d_5_i_)) and ((d_5_i_) < (len(odd__collatz)))) or (((odd__collatz)[d_5_i_]) == (next__odd__collatz((odd__collatz)[(d_5_i_) - (1)]))), [[next__odd__collatz((odd__collatz)[(d_5_i_) - (1)])]])))
    while ((odd__collatz)[(len(odd__collatz)) - (1)]) != (1):
        Invariant(Acc(list_pred(odd__collatz)))
        Invariant((d_3_cur_) > (0))
        Invariant((len(odd__collatz)) > (0))
        Invariant(Forall(int, lambda d_4_i_:
            (not (((0) <= (d_4_i_)) and ((d_4_i_) < (len(odd__collatz)))) or ((((odd__collatz)[d_4_i_] > 0))))))
        Invariant(Forall(int, lambda d_4_i_:
            (not (((0) <= (d_4_i_)) and ((d_4_i_) < (len(odd__collatz)))) or ((((odd__collatz)[d_4_i_] % 2)) == (1)))))
        Invariant(Forall(int, lambda d_5_i_:
            (not (((1) <= (d_5_i_)) and ((d_5_i_) < (len(odd__collatz)))) or (((odd__collatz)[d_5_i_]) == (next__odd__collatz((odd__collatz)[(d_5_i_) - (1)]))), [[next__odd__collatz((odd__collatz)[(d_5_i_) - (1)])]])))
        odd__collatz = (odd__collatz) + [next__odd__collatz((odd__collatz)[(len(odd__collatz)) - (1)])]
        Assert(Forall(int, lambda d_5_i_:
            (not (((1) <= (d_5_i_)) and ((d_5_i_) < (len(odd__collatz)))) or (((odd__collatz)[d_5_i_]) == (next__odd__collatz((odd__collatz)[(d_5_i_) - (1)]))), [[next__odd__collatz((odd__collatz)[(d_5_i_) - (1)])]])))
    return odd__collatz


def get__odd__collatz(n : int) -> List[int]:
    Requires((n) > (1))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_6_i_:
        Forall(int, lambda d_7_j_:
            not ((((0) <= (d_6_i_)) and ((d_6_i_) < (d_7_j_))) and ((d_7_j_) < (len(Result())))) or (((Result())[d_6_i_]) <= ((Result())[d_7_j_])))))
    Ensures(Forall(int, lambda d_8_i_:
        not (((0) <= (d_8_i_)) and ((d_8_i_) < (len(Result())))) or ((((Result())[d_8_i_] % 2)) == (1))))
    sorted = list([int(0)] * 0) # type : List[int]
    sorted = get__odd__collatz__unsorted(n)
    d_12_unsorted_ = list(sorted) # type : List[int]
    d_9_i_ = int(0) # type : int
    d_9_i_ = 0
    while (d_9_i_) < (len(sorted)):
        Invariant(Acc(list_pred(sorted)))
        Invariant(Acc(list_pred(d_12_unsorted_)))
        Invariant(((0) <= (d_9_i_)) and ((d_9_i_) <= (len(sorted))))
        Invariant(Forall(int, lambda d_8_i_:
            not (((0) <= (d_8_i_)) and ((d_8_i_) < (len(sorted)))) or ((((sorted)[d_8_i_] % 2)) == (1))))
        Invariant((len(sorted)) == (len(d_12_unsorted_)))
        Invariant(Forall(int, lambda d_10_j_:
            (Forall(int, lambda d_11_k_:
                (not ((((0) <= (d_10_j_)) and ((d_10_j_) < (d_11_k_))) and ((d_11_k_) < (d_9_i_))) or (((sorted)[d_10_j_]) <= ((sorted)[d_11_k_])), 
                    [[(sorted)[d_11_k_]]])), 
                [[sorted[d_10_j_]]])))
        Invariant(Forall(int, lambda d_12_j_:
            (not ((((0) <= (d_12_j_)) and ((d_12_j_) < (d_9_i_)))) or 
                (Forall(int, lambda d_13_k_:
                    (not ((((d_9_i_) <= (d_13_k_)) and ((d_13_k_) < (len(sorted))))) or 
                        (((sorted)[d_12_j_]) <= ((sorted)[d_13_k_])), [[sorted[d_13_k_]]]))), [[(sorted)[d_12_j_]]])))
        d_15_minIndex_ = int(0) # type : int
        d_15_minIndex_ = d_9_i_
        d_16_j_ = int(0) # type : int
        d_16_j_ = (d_9_i_) + (1)
        while (d_16_j_) < (len(sorted)):
            Invariant(Acc(list_pred(sorted)))
            Invariant(Acc(list_pred(d_12_unsorted_)))
            Invariant((len(sorted)) == (len(d_12_unsorted_)))
            Invariant(((0) <= (d_9_i_)) and ((d_9_i_) < (len(sorted))))
            Invariant((((d_9_i_) <= (d_15_minIndex_)) and ((d_15_minIndex_) < (d_16_j_))) and ((d_16_j_) <= (len(sorted))))
            Invariant(Forall(int, lambda d_8_i_:
                not (((0) <= (d_8_i_)) and ((d_8_i_) < (len(sorted)))) or ((((sorted)[d_8_i_] % 2)) == (1))))
            Invariant(Forall(int, lambda d_10_j_:
                (Forall(int, lambda d_11_k_:
                    (not ((((0) <= (d_10_j_)) and ((d_10_j_) < (d_11_k_))) and ((d_11_k_) < (d_9_i_))) or (((sorted)[d_10_j_]) <= ((sorted)[d_11_k_])), 
                        [[(sorted)[d_11_k_]]])), 
                    [[sorted[d_10_j_]]])))
            Invariant(Forall(int, lambda d_12_j_:
                (not ((((0) <= (d_12_j_)) and ((d_12_j_) < (d_9_i_)))) or 
                    (Forall(int, lambda d_13_k_:
                        (not ((((d_9_i_) <= (d_13_k_)) and ((d_13_k_) < (len(sorted))))) or 
                            (((sorted)[d_12_j_]) <= ((sorted)[d_13_k_])), [[sorted[d_13_k_]]]))), [[(sorted)[d_12_j_]]])))
            Invariant(Forall(int, lambda d_17_k_:
                (not (((d_9_i_) <= (d_17_k_)) and ((d_17_k_) < (d_16_j_))) or (((sorted)[d_15_minIndex_]) <= ((sorted)[d_17_k_])), [[(sorted)[d_17_k_]]])))
            if ((sorted)[d_16_j_]) < ((sorted)[d_15_minIndex_]):
                d_15_minIndex_ = d_16_j_
            d_16_j_ = (d_16_j_) + (1)
        if (d_15_minIndex_) != (d_9_i_):
            rhs0_ = (sorted)[d_9_i_] # type : int
            (sorted)[d_9_i_] = (sorted)[d_15_minIndex_]
            (sorted)[d_15_minIndex_] = rhs0_
        d_9_i_ = (d_9_i_) + (1)
    return sorted

