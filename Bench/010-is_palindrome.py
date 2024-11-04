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
    Ensures((Result()) == (Forall(int, lambda d_0_k_:
        not (((start) <= (d_0_k_)) and ((d_0_k_) < (len(s)))) or (((s)[d_0_k_]) == ((s)[((len(s)) - (1)) - (d_0_k_ - start)])))))
    Ensures(Result() == is__palindrome__fun(start, s))
    # post-conditions-end

    # impl-start
    d_1_i_ : int = start
    d_2_j_ : int = (len(s)) - (1)
    while (d_1_i_) < (d_2_j_):
        # invariants-start
        Invariant(Acc(list_pred(s), 1/2))
        Invariant(((0) <= (start)) and ((start) < (len(s))))
        Invariant(d_1_i_ <= d_2_j_ + 1)
        Invariant(((start) <= (d_1_i_)) and ((d_1_i_) < (len(s))))
        Invariant(((start) <= (d_2_j_)) and ((d_2_j_) < (len(s))))
        Invariant((d_2_j_ - start) == (((len(s)) - (d_1_i_)) - (1)))
        Invariant(Forall(int, lambda d_3_k_:
            not (((start) <= (d_3_k_)) and ((d_3_k_) < (d_1_i_))) or (((s)[d_3_k_]) == ((s)[((len(s)) - (1)) - (d_3_k_ - start)]))))
        # invariants-end
        if ((s)[d_1_i_]) != ((s)[d_2_j_]):
            return False
        d_1_i_ = (d_1_i_) + (1)
        d_2_j_ = (d_2_j_) - (1)
    return True
    # impl-end

@Pure
def is__palindrome__fun(start : int, s : List[int]) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(0 <= start and start < len(s))
    # pre-conditions-end

    # impl-start
    return Forall(int, lambda d_4_k_:
        not (((start) <= (d_4_k_)) and ((d_4_k_) < (len(s)))) or (((s)[d_4_k_]) == ((s)[((len(s)) - (1)) - (d_4_k_ - start)])))
    # impl-end

@Pure
def starts__with(result : List[int], s : List[int]) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(Acc(list_pred(result), 1/2))
    # pre-conditions-end

    # impl-start
    return ((len(result)) >= (len(s))) and (Forall(int, lambda d_5_k_:
        not (((0) <= (d_5_k_)) and ((d_5_k_) < (len(s)))) or (((result)[d_5_k_]) == ((s)[d_5_k_]))))
    # impl-end

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
    d_6_beginning__of__suffix_ : int = int(0)
    d_8_flag_ : bool = is__palindrome(d_6_beginning__of__suffix_, s)
    while not(d_8_flag_):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(len(s) > 0)
        Invariant((((d_6_beginning__of__suffix_) >= (0)) and (((d_6_beginning__of__suffix_) + (1)) < (len(s)))) or ((d_8_flag_) and (((d_6_beginning__of__suffix_) >= (0)) and ((d_6_beginning__of__suffix_) < (len(s))))))
        Invariant(Implies(d_8_flag_, is__palindrome__fun(d_6_beginning__of__suffix_, s)))
        # invariants-end
        d_6_beginning__of__suffix_ = (d_6_beginning__of__suffix_) + (1)
        d_8_flag_ = is__palindrome(d_6_beginning__of__suffix_, s)
    d_10_reversed_ : List[int] = reverse(d_6_beginning__of__suffix_, s)
    result = (s) + (d_10_reversed_)
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
    Ensures(Forall(int, lambda d_11_k_:
        not (((0) <= (d_11_k_)) and ((d_11_k_) < (end))) or (((Result())[d_11_k_]) == ((str)[((end) - (1)) - (d_11_k_)]))))
    # post-conditions-end

    # impl-start
    rev : List[int] = []
    d_12_i_ : int = 0
    while (d_12_i_) < (end):
        # invariants-start
        Invariant(Acc(list_pred(str), 1/2))
        Invariant(Acc(list_pred(rev)))
        Invariant(0 <= end and end < len(str))
        Invariant(((d_12_i_) >= (0)) and ((d_12_i_) <= (end)))
        Invariant((len(rev)) == (d_12_i_))
        Invariant(Forall(int, lambda d_13_k_:
            not (((0) <= (d_13_k_)) and ((d_13_k_) < (d_12_i_))) or (((rev)[d_13_k_]) == ((str)[(end - (1)) - (d_13_k_)]))))
        # invariants-end
        rev = (rev) + [(str)[(end - (d_12_i_)) - (1)]]
        d_12_i_ = (d_12_i_) + (1)
    return rev
    # impl-end
