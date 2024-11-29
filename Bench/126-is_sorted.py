from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *


def is__sorted(a : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a)))
    Ensures((Result()) == (
        Forall(int, lambda d_0_i_:
            Forall(int, lambda d_1_j_:
                not ((((0) <= (d_0_i_)) and ((d_0_i_) <= (d_1_j_))) and ((d_1_j_) < (len(a)))) or ((((a)[d_0_i_]) <= ((a)[d_1_j_])))))
        and (Forall(int, lambda d_2_i_:
                    not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(a)))) or ((count_set(a, (a)[d_2_i_], 0)) <= (2))))))
    # post-conditions-end
    # impl-start
    if (len(a)) == (0):
        # assert-start
        Assert(Forall(int, lambda d_0_i_:
            Forall(int, lambda d_1_j_:
                not ((((0) <= (d_0_i_)) and ((d_0_i_) <= (d_1_j_))) and ((d_1_j_) < (len(a)))) or ((((a)[d_0_i_]) <= ((a)[d_1_j_]))))))
        # assert-end
        return True
    d_3_is__asc_ : bool = True
    d_4_i_ : int = 1
    while (d_4_i_) < (len(a)):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(((1) <= (d_4_i_)) and ((d_4_i_) <= (len(a))))
        Invariant((d_3_is__asc_) == (Forall(int, lambda d_5_j_:
            Forall(int, lambda d_6_k_:
                not ((((0) <= (d_5_j_)) and ((d_5_j_) < (d_6_k_))) and ((d_6_k_) < (d_4_i_))) or (((a)[d_5_j_]) <= ((a)[d_6_k_]))))))
        # invariants-end
        if ((a)[(d_4_i_) - (1)]) > ((a)[d_4_i_]):
            d_3_is__asc_ = False
        d_4_i_ = (d_4_i_) + (1)
    if not(d_3_is__asc_):
        return False
    d_4_i_ = 0
    d_7_has__no__more__that__2_ : bool = True
    while (d_4_i_) < (len(a)):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(((0) <= (d_4_i_)) and ((d_4_i_) <= (len(a))))
        Invariant((d_3_is__asc_) == 
            (Forall(int, lambda d_5_j_:
                Forall(int, lambda d_6_k_:
                    not ((((0) <= (d_5_j_)) and ((d_5_j_) < (d_6_k_))) and ((d_6_k_) < (len(a)))) or (((a)[d_5_j_]) <= ((a)[d_6_k_]))))))
        Invariant((d_7_has__no__more__that__2_) == (Forall(int, lambda d_8_j_:
            not (((0) <= (d_8_j_)) and ((d_8_j_) < (d_4_i_))) or ((count_set(a, (a)[d_8_j_], 0)) <= (2))) and 
            (Forall(int, lambda d_5_j_:
                Forall(int, lambda d_6_k_:
                    not ((((0) <= (d_5_j_)) and ((d_5_j_) < (d_6_k_))) and ((d_6_k_) < (len(a)))) or (((a)[d_5_j_]) <= ((a)[d_6_k_])))))))
        # invariants-end
        d_9_count_ : int = count_set(a, (a)[d_4_i_], 0)
        if (d_9_count_) > (2):
            d_7_has__no__more__that__2_ = False
        d_4_i_ = (d_4_i_) + (1)
    f : bool = d_7_has__no__more__that__2_
    return f
    # impl-end

@Pure
def count_set(a : List[int], x : int, i : int) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(a), 1/2))
    Requires(((0) <= (i)) and ((i) <= (len(a))))
    # pre-conditions-end
    # post-conditions-start
    # post-conditions-end

    # pure-start
    if (i) == 0:
        return 0
    else:
        return (count_set(a, x, (i) - (1))) + (((a)[(i) - (1)]) == (x))
    # pure-end
