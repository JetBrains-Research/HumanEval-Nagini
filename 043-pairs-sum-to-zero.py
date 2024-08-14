from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def pairs__sum__to__zero(l : List[int]) -> bool:
    Requires(Acc(list_pred(l)))
    Ensures(Acc(list_pred(l)))
    Ensures(not (Result()) or (Exists(int, lambda d_0_i_:
        Exists(int, lambda d_1_j_:
            (((((0) <= (d_0_i_)) and ((d_0_i_) < (len(l)))) and (((0) <= (d_1_j_)) and ((d_1_j_) < (len(l))))) and ((d_0_i_) != (d_1_j_))) and ((((l)[d_0_i_]) + ((l)[d_1_j_])) == (0))))))
    Ensures(not (not(Result())) or (Forall(int, lambda d_2_i_:
        Forall(int, lambda d_3_j_:
            (not (((((0) <= (d_2_i_)) and ((d_2_i_) < (len(l)))) and (((0) <= (d_3_j_)) and ((d_3_j_) < (len(l))))) and ((d_2_i_) != (d_3_j_))) or ((((l)[d_2_i_]) + ((l)[d_3_j_])) != (0)), [[((l)[d_2_i_]) + ((l)[d_3_j_])]])))))
    result = False # type : bool
    result = False
    d_4_i_ = int(0) # type : int
    d_4_i_ = 0
    while (d_4_i_) < (len(l)):
        Invariant(Acc(list_pred(l)))
        Invariant(((d_4_i_) >= (0)) and ((d_4_i_) <= (len(l))))
        Invariant(Implies(not(result), Forall(int, lambda d_5_i1_:
            Forall(int, lambda d_6_j_:
                (Implies(((((0) <= (d_5_i1_)) and ((d_5_i1_) < (d_4_i_))) and (((0) <= (d_6_j_)) and ((d_6_j_) < (len(l))))) and ((d_5_i1_) != (d_6_j_)), (((l)[d_5_i1_]) + ((l)[d_6_j_])) != (0)), [[((l)[d_5_i1_]) + ((l)[d_6_j_])]])))))
        Invariant(not (result) or (Exists(int, lambda d_7_i1_:
            Exists(int, lambda d_8_j_:
                (((((0) <= (d_7_i1_)) and ((d_7_i1_) < (d_4_i_))) and (((0) <= (d_8_j_)) and ((d_8_j_) < (len(l))))) and ((d_7_i1_) != (d_8_j_))) and ((((l)[d_7_i1_]) + ((l)[d_8_j_])) == (0))))))
        d_9_j_ = int(0) # type : int
        d_9_j_ = 0
        while (d_9_j_) < (len(l)):
            Invariant(Acc(list_pred(l)))
            Invariant(((d_4_i_) >= (0)) and ((d_4_i_) < (len(l))))
            Invariant(((d_9_j_) >= (0)) and ((d_9_j_) <= (len(l))))
            Invariant(Implies(not(result), Forall(int, lambda d_5_i1_:
                Forall(int, lambda d_6_j_:
                    (Implies((((((0) <= (d_5_i1_)) and ((d_5_i1_) < (d_4_i_))) and (((0) <= (d_6_j_)) and ((d_6_j_) < (len(l))))) or (d_5_i1_ == d_4_i_ and ((0) <= (d_6_j_)) and ((d_6_j_) < (d_9_j_)))) and ((d_5_i1_) != (d_6_j_)), (((l)[d_5_i1_]) + ((l)[d_6_j_])) != (0)), [[((l)[d_5_i1_]) + ((l)[d_6_j_])]])))))
            Invariant(not (result) or ((Exists(int, lambda d_13_i1_:
                Exists(int, lambda d_14_j1_:
                    (((((0) <= (d_13_i1_)) and ((d_13_i1_) < (d_4_i_))) and (((0) <= (d_14_j1_)) and ((d_14_j1_) < (len(l))))) and ((d_13_i1_) != (d_14_j1_))) and ((((l)[d_13_i1_]) + ((l)[d_14_j1_])) == (0))))) or (Exists(int, lambda d_15_j1_:
                ((((0) <= (d_15_j1_)) and ((d_15_j1_) < (d_9_j_))) and ((d_4_i_) != (d_15_j1_))) and ((((l)[d_4_i_]) + ((l)[d_15_j1_])) == (0))))))
            if ((d_4_i_) != (d_9_j_)) and ((((l)[d_4_i_]) + ((l)[d_9_j_])) == (0)):
                result = True
            d_9_j_ = (d_9_j_) + (1)
        d_4_i_ = (d_4_i_) + (1)
    return result