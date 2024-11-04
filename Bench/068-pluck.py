from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def PluckSmallestEven(nodes : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(nodes)))
    Requires((len(nodes)) <= (10000))
    Requires(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(nodes)))) or (((nodes)[d_0_i_]) >= (0))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(nodes)))
    Ensures(Acc(list_pred(Result())))
    Ensures(((len(Result())) == (0)) or ((len(Result())) == (2)))
    Ensures(not ((len(Result())) == (2)) or ((((0) <= ((Result())[1])) and (((Result())[1]) < (len(nodes)))) and (((nodes)[(Result())[1]]) == ((Result())[0]))))
    Ensures(not ((len(Result())) == (2)) or ((((Result())[0] % 2)) == (0)))
    Ensures(not ((len(Result())) == (2)) or (Forall(int, lambda d_1_i_:
        not ((((0) <= (d_1_i_)) and ((d_1_i_) < (len(nodes)))) and ((((nodes)[d_1_i_] % 2)) == (0))) or (((Result())[0]) <= ((nodes)[d_1_i_])))))
    Ensures(not ((len(Result())) == (2)) or (Forall(int, lambda d_2_i_:
        not (((0) <= (d_2_i_)) and ((d_2_i_) < ((Result())[1]))) or (((((nodes)[d_2_i_] % 2)) != (0)) or (((nodes)[d_2_i_]) > ((Result())[0]))))))
    Ensures(not ((len(Result())) == (0)) or (Forall(int, lambda d_3_i_:
        not (((0) <= (d_3_i_)) and ((d_3_i_) < (len(nodes)))) or ((((nodes)[d_3_i_] % 2)) != (0)))))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    d_4_smallestEven_ : int = -1
    d_5_smallestIndex_ : int = -1
    d_6_i_ : int = int(0)
    while d_6_i_ < len(nodes):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(nodes)))
        Invariant(((0) <= (d_6_i_)) and ((d_6_i_) <= (len(nodes))))
        Invariant(((d_4_smallestEven_) == (-1)) == ((d_5_smallestIndex_) == (-1)))
        Invariant(not ((d_5_smallestIndex_) != (-1)) or (((0) <= (d_5_smallestIndex_)) and ((d_5_smallestIndex_) < (d_6_i_))))
        Invariant(not ((d_5_smallestIndex_) != (-1)) or (((nodes)[d_5_smallestIndex_]) == (d_4_smallestEven_)))
        Invariant(not ((d_4_smallestEven_) != (-1)) or (((d_4_smallestEven_ % 2)) == (0)))
        Invariant(not ((d_4_smallestEven_) != (-1)) or (Forall(int, lambda d_7_j_:
            (not ((((0) <= (d_7_j_)) and ((d_7_j_) < (d_6_i_))) and ((((nodes)[d_7_j_] % 2)) == (0))) or ((d_4_smallestEven_) <= ((nodes)[d_7_j_])), [[(nodes)[d_7_j_]]]))))
        Invariant(not ((d_5_smallestIndex_) != (-1)) or (Forall(int, lambda d_8_j_:
            (not (((0) <= (d_8_j_)) and ((d_8_j_) < (d_5_smallestIndex_))) or ((((nodes)[d_8_j_] % 2)) != (0)) or (((nodes)[d_8_j_]) > (d_4_smallestEven_)), [[(nodes)[d_8_j_]]]))))
        Invariant(not ((d_5_smallestIndex_) == (-1)) or (Forall(int, lambda d_9_j_:
            (not (((0) <= (d_9_j_)) and ((d_9_j_) < (d_6_i_))) or ((((nodes)[d_9_j_] % 2)) != (0)), [[(nodes)[d_9_j_]]]))))
        # invariants-end
        if ((((nodes)[d_6_i_] % 2)) == (0)) and (((d_4_smallestEven_) == (-1)) or (((nodes)[d_6_i_]) < (d_4_smallestEven_))):
            d_4_smallestEven_ = (nodes)[d_6_i_]
            d_5_smallestIndex_ = d_6_i_
        d_6_i_ = d_6_i_ + 1
    if (d_5_smallestIndex_) == (-1):
        result = list([])
        return result
    else:
        result = list([d_4_smallestEven_, d_5_smallestIndex_])
        return result
    # impl-end
