from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def encode(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(s)))) or ((((97) <= ((s)[d_0_i_])) and (((s)[d_0_i_]) <= (122))) or (((65) <= ((s)[d_0_i_])) and (((s)[d_0_i_]) <= (90))))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures(Acc(list_pred(s)))
    Ensures((len(s)) == (len(Result())))
    Ensures(Forall(int, lambda d_1_i_:
        not ((((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) and (is__vowel((s)[d_1_i_]))) or (((Result())[d_1_i_]) == (rot2(swap__case((s)[d_1_i_]))))))
    Ensures(Forall(int, lambda d_2_i_:
        not ((((0) <= (d_2_i_)) and ((d_2_i_) < (len(s)))) and (not(is__vowel((s)[d_2_i_])))) or (((Result())[d_2_i_]) == (swap__case((s)[d_2_i_])))))
    # post-conditions-end

    # impl-start
    t : List[int] = []
    d_3_i_ : int = 0
    while (d_3_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(t)))
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= (len(s))))
        Invariant((len(t)) == (d_3_i_))
        Invariant(Forall(int, lambda d_4_j_:
            (not ((((0) <= (d_4_j_)) and ((d_4_j_) < (d_3_i_))) and (is__vowel((s)[d_4_j_]))) or (((t)[d_4_j_]) == (rot2(swap__case((s)[d_4_j_])))), [[rot2(swap__case((s)[d_4_j_]))]])))
        Invariant(Forall(int, lambda d_5_j_:
            (not ((((0) <= (d_5_j_)) and ((d_5_j_) < (d_3_i_))) and (not(is__vowel((s)[d_5_j_])))) or (((t)[d_5_j_]) == (swap__case((s)[d_5_j_]))), [[swap__case((s)[d_5_j_])]])))
        # invariants-end
        if is__vowel((s)[d_3_i_]):
            t = (t) + [rot2(swap__case((s)[d_3_i_]))]
        else:
            t = (t) + [swap__case((s)[d_3_i_])]
        d_3_i_ = (d_3_i_) + (1)
    return t
    # impl-end

@Pure
def swap__case(c : int) -> int :
    # pure-start
    if ((97) <= (c)) and ((c) <= (122)):
        return (65) + ((c) - (97))
    elif True:
        return (97) + ((c) - (65))
    # pure-end

@Pure
def rot2(c : int) -> int :
    # pure-start
    return (c + 2)  
    # pure-end

@Pure
def is__vowel(c : int) -> bool :
    # pure-start
    return ((((((c) == (97)) or ((c) == (101))) or ((c) == (105))) or ((c) == (111))) or ((c) == (117))) or ((((((c) == (65)) or ((c) == (69))) or ((c) == (73))) or ((c) == (79))) or ((c) == (85)))
    # pure-end
