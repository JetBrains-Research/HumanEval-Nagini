from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def get__positive(l : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(l)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(l)))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(Result())))) or (((Result())[d_0_i_]) > (0))))
    Ensures((len(Result())) <= (len(l)))
    Ensures(Forall(int, lambda d_1_i1_:
        not (((d_1_i1_) >= (0)) and ((d_1_i1_) < (len(l)))) or (not (((l)[d_1_i1_]) > (0)) or (Exists(int, lambda d_2_i2_:
            (((d_2_i2_) >= (0)) and ((d_2_i2_) < (len(Result())))) and (((Result())[d_2_i2_]) == ((l)[d_1_i1_])))))))
    Ensures(((len(Result())) == (0)) or (Forall(int, lambda d_3_i1_:
        not (((d_3_i1_) >= (0)) and ((d_3_i1_) < (len(Result())))) or (Exists(int, lambda d_4_i2_:
            (((d_4_i2_) >= (0)) and ((d_4_i2_) < (len(l)))) and (((l)[d_4_i2_]) == ((Result())[d_3_i1_])))))))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    d_5_i_ : int = 0
    while (d_5_i_) < (len(l)):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(l)))
        Invariant(((d_5_i_) >= (0)) and ((d_5_i_) <= (len(l))))
        Invariant((len(result)) <= (d_5_i_))
        Invariant(Forall(int, lambda d_6_i1_:
            not (((d_6_i1_) >= (0)) and ((d_6_i1_) < (len(result)))) or (((result)[d_6_i1_]) > (0))))
        Invariant(not ((d_5_i_) > (0)) or (not (((l)[(d_5_i_) - (1)]) > (0)) or (Exists(int, lambda d_7_i2_:
            (((d_7_i2_) >= (0)) and ((d_7_i2_) < (len(result)))) and (((result)[d_7_i2_]) == ((l)[(d_5_i_) - (1)]))))))
        Invariant(Forall(int, lambda d_9_i1_:
            not (((d_9_i1_) >= (0)) and ((d_9_i1_) < (d_5_i_))) or (not (((l)[d_9_i1_]) > (0)) or (Exists(int, lambda d_10_i2_:
                (((d_10_i2_) >= (0)) and ((d_10_i2_) < (len(result)))) and (((result)[d_10_i2_]) == ((l)[d_9_i1_])))))))
        Invariant(((len(result)) == (0)) or (Forall(int, lambda d_11_i1_:
            not (((d_11_i1_) >= (0)) and ((d_11_i1_) < (len(result)))) or (Exists(int, lambda d_12_i2_:
                (((d_12_i2_) >= (0)) and ((d_12_i2_) < (len(l)))) and (((l)[d_12_i2_]) == ((result)[d_11_i1_])))))))
        # invariants-end
        d_13_n_ : int = (l)[d_5_i_]
        if (d_13_n_) > (0):
            d_17_res__prev_ = result
            # assert-start
            Assert(Forall(int, lambda d_14_i1_:
                not (((d_14_i1_) >= (0)) and ((d_14_i1_) < (d_5_i_))) or (not (((l)[d_14_i1_]) > (0)) or (Exists(int, lambda d_15_i2_:
                    (((d_15_i2_) >= (0)) and ((d_15_i2_) < (len(result)))) and (((result)[d_15_i2_]) == ((l)[d_14_i1_])))))))
            # assert-end
            result = (result) + ([d_13_n_])
            # assert-start
            Assert(((result)[(len(result)) - (1)]) == (d_13_n_))
            Assert(Forall(int, lambda d_16_i1_:
                not (((d_16_i1_) >= (0)) and ((d_16_i1_) < (len(d_17_res__prev_)))) or (((d_17_res__prev_)[d_16_i1_]) == ((result)[d_16_i1_]))))
            Assert(Forall(int, lambda d_18_i1_:
                not (((d_18_i1_) >= (0)) and ((d_18_i1_) < (d_5_i_))) or (not (((l)[d_18_i1_]) > (0)) or (Exists(int, lambda d_19_i2_:
                    (((d_19_i2_) >= (0)) and ((d_19_i2_) < (len(d_17_res__prev_)))) and (((d_17_res__prev_)[d_19_i2_]) == ((l)[d_18_i1_])))))))
            # assert-end
        d_5_i_ = (d_5_i_) + (1)
    return result
    # impl-end