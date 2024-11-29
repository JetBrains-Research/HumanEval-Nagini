from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def xor(a : int, b : int) -> int:
    # pre-conditions-start
    Ensures((Result()) == ((0 if (a) == (b) else 1)))
    # pre-conditions-end

    # pure-start
    result : int = int(0)
    if (a) == (b):
        result = 0
    else:
        result = 1
    return result
    # pure-end

def string__xor(a : List[int], b : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(b)))
    Requires(Acc(list_pred(a)))
    Requires((len(a)) == (len(b)))
    Requires(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(a)))) or ((((a)[d_0_i_]) == (0)) or (((a)[d_0_i_]) == (1)))))
    Requires(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(b)))) or ((((b)[d_1_i_]) == (0)) or (((b)[d_1_i_]) == (1)))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(b)))
    Ensures(Acc(list_pred(a)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(a)) == (len(b)))
    Ensures((len(Result())) == (len(a)))
    Ensures(Forall(int, lambda d_2_i_:
        not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(Result())))) or ((((Result())[d_2_i_]) == (0)) or (((Result())[d_2_i_]) == (1)))))
    Ensures(Forall(int, lambda d_3_i_:
        not (((0) <= (d_3_i_)) and ((d_3_i_) < (len(Result())))) or (((Result())[d_3_i_]) == ((0 if ((a)[d_3_i_]) == ((b)[d_3_i_]) else 1)))))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    d_4_i_ : int = int(0)
    while (d_4_i_) < (len(a)):
        # invariants-start
        Invariant(Acc(list_pred(b)))
        Invariant(Acc(list_pred(a)))
        Invariant(Acc(list_pred(result))) 
        Invariant((len(a)) == (len(b)))
        Invariant(((d_4_i_) >= (0)) and ((d_4_i_) <= (len(a))))
        Invariant((len(result)) == (d_4_i_))
        Invariant(Forall(int, lambda d_0_i_:
            not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(a)))) or ((((a)[d_0_i_]) == (0)) or (((a)[d_0_i_]) == (1)))))
        Invariant(Forall(int, lambda d_1_i_:
            not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(b)))) or ((((b)[d_1_i_]) == (0)) or (((b)[d_1_i_]) == (1)))))
        Invariant(Forall(int, lambda d_5_j_:
            not (((0) <= (d_5_j_)) and ((d_5_j_) < (d_4_i_))) or (((result)[d_5_j_]) == ((0 if ((a)[d_5_j_]) == ((b)[d_5_j_]) else 1)))))
        # invariants-end
        d_6_bitResult_ = (0 if ((a)[d_4_i_]) == ((b)[d_4_i_]) else 1)
        result = (result) + [d_6_bitResult_]
        d_4_i_ = (d_4_i_) + (1)
    return result
    # impl-end
