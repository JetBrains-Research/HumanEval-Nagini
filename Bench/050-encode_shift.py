from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure 
def encode__char(c : int) -> int :
    # impl-start
    return (c - 97 + 5) % 26 + 97
    # impl-end

@Pure 
def decode__char(c : int) -> int :
    # impl-start
    return ((c) - (97) - (5)) % 26 + 97
    # impl-end

def encode__shift(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(s)))) or (((97) <= ((s)[d_0_i_])) and (((s)[d_0_i_]) <= (122)))))
    # pre-conditions-end
    # post-conditions-start 
    Ensures(Acc(list_pred(Result())))
    Ensures(Acc(list_pred(s)))
    Ensures((len(s)) == (len(Result())))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) or (((Result())[d_1_i_]) == (encode__char((s)[d_1_i_])))))
    # post-conditions-end

    # impl-start
    t : List[int] = [] # type : List[int]
    d_2_i_ = int(0) # type : int
    d_2_i_ = 0
    while (d_2_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(t)))
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_2_i_)) and ((d_2_i_) <= (len(s))))
        Invariant((len(t)) == (d_2_i_))
        Invariant(Forall(int, lambda d_3_j_:
            (not (((0) <= (d_3_j_)) and ((d_3_j_) < (d_2_i_))) or (((t)[d_3_j_]) == (encode__char((s)[d_3_j_]))), [[encode__char((s)[d_3_j_])]])))
        # invariants-end
        t = (t) + [encode__char((s)[d_2_i_])]
        d_2_i_ = (d_2_i_) + (1)
    return t
    # impl-end

def decode__shift(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_4_i_:
        not (((0) <= (d_4_i_)) and ((d_4_i_) < (len(s)))) or (((97) <= ((s)[d_4_i_])) and (((s)[d_4_i_]) <= (122)))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures(Acc(list_pred(s)))
    Ensures((len(s)) == (len(Result())))
    Ensures(Forall(int, lambda d_5_i_:
        not (((0) <= (d_5_i_)) and ((d_5_i_) < (len(s)))) or (((Result())[d_5_i_]) == (decode__char((s)[d_5_i_])))))
    # post-conditions-end

    # impl-start
    t : List[int] = []
    d_6_i_ = int(0) # type : int
    d_6_i_ = 0
    while (d_6_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(t)))
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_6_i_)) and ((d_6_i_) <= (len(s))))
        Invariant((len(t)) == (d_6_i_))
        Invariant(Forall(int, lambda d_7_j_:
            (not (((0) <= (d_7_j_)) and ((d_7_j_) < (d_6_i_))) or (((t)[d_7_j_]) == (decode__char((s)[d_7_j_]))), [[decode__char((s)[d_7_j_])]])))
        # invariants-end
        t = (t) + [decode__char((s)[d_6_i_])]
        d_6_i_ = (d_6_i_) + (1)
    return t
    # impl-end
