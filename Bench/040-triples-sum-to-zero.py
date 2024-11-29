from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def triples__sum__to__zero(l : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(l)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(l)))
    Ensures(Implies(not(Result()), Forall(int, lambda d_3_i_:
        Forall(int, lambda d_4_j_:
            Forall(int, lambda d_5_k_:
                Implies((((((((0) <= (d_3_i_)) and ((d_3_i_) < (len(l)))) and (((0) <= (d_4_j_)) and ((d_4_j_) < (len(l))))) and (((0) <= (d_5_k_)) and ((d_5_k_) < (len(l))))) and ((d_3_i_) != (d_4_j_))) and ((d_4_j_) != (d_5_k_))) and ((d_3_i_) != (d_5_k_)), ((((l)[d_3_i_]) + ((l)[d_4_j_])) + ((l)[d_5_k_])) != (0)))))))
    Ensures(Implies(Result(), Exists(int, lambda d_0_i_:
        Exists(int, lambda d_1_j_:
            Exists(int, lambda d_2_k_:
                ((((((((0) <= (d_0_i_)) and ((d_0_i_) < (len(l)))) and (((0) <= (d_1_j_)) and ((d_1_j_) < (len(l))))) and (((0) <= (d_2_k_)) and ((d_2_k_) < (len(l))))) and ((d_0_i_) != (d_1_j_))) and ((d_1_j_) != (d_2_k_))) and ((d_0_i_) != (d_2_k_))) and (((((l)[d_0_i_]) + ((l)[d_1_j_])) + ((l)[d_2_k_])) == (0)))))))
    # post-conditions-end

    # impl-start
    d_6_i_ : int = 0
    while (d_6_i_) < (len(l)):
        # invariants-start
        Invariant(Acc(list_pred(l), 1/2))
        Invariant(((d_6_i_) >= (0)) and ((d_6_i_) <= (len(l))))
        Invariant(Forall(int, lambda d_7_i1_:
            Forall(int, lambda d_8_j_:
                Forall(int, lambda d_9_k_:
                    (Implies((((((((0) <= (d_7_i1_)) and ((d_7_i1_) < (d_6_i_))) and (((0) <= (d_8_j_)) and ((d_8_j_) < (len(l))))) and (((0) <= (d_9_k_)) and ((d_9_k_) < (len(l))))) and ((d_7_i1_) != (d_8_j_))) and ((d_8_j_) != (d_9_k_))) and ((d_7_i1_) != (d_9_k_)), ((((l)[d_7_i1_]) + ((l)[d_8_j_])) + ((l)[d_9_k_])) != (0)), [[(((l)[d_7_i1_]) + ((l)[d_8_j_])) + ((l)[d_9_k_])]])))))
        # invariants-end
        d_13_j_ : int = 0
        while (d_13_j_) < (len(l)):
            # invariants-start
            Invariant(Acc(list_pred(l), 1/2))
            Invariant(((d_6_i_) >= (0)) and ((d_6_i_) < (len(l))))
            Invariant(((d_13_j_) >= (0)) and ((d_13_j_) <= (len(l))))
            Invariant(Forall(int, lambda d_14_i1_:
                Forall(int, lambda d_15_j_:
                    Forall(int, lambda d_16_k_:
                        (Implies(((((((((0) <= (d_14_i1_)) and ((d_14_i1_) < (d_6_i_))) and (((0) <= (d_15_j_)) and ((d_15_j_) < (len(l))))) and (((0) <= (d_16_k_)) and ((d_16_k_) < (len(l)))))) or 
                                (d_14_i1_ == d_6_i_ and (d_15_j_) >= 0 and (d_15_j_) < d_13_j_ and (d_16_k_) >= 0 and (d_16_k_) < len(l)))
                                and ((d_14_i1_) != (d_15_j_)) and ((d_15_j_) != (d_16_k_))) and ((d_14_i1_) != (d_16_k_)), ((((l)[d_14_i1_]) + ((l)[d_15_j_])) + ((l)[d_16_k_])) != (0)), [[(((l)[d_14_i1_]) + ((l)[d_15_j_])) + ((l)[d_16_k_])]])))))
            # invariants-end
            d_24_k_ : int = 0
            while (d_24_k_) < (len(l)):
                # invariants-start
                Invariant(Acc(list_pred(l), 1/2))
                Invariant(((d_6_i_) >= (0)) and ((d_6_i_) < (len(l))))
                Invariant(((d_13_j_) >= (0)) and ((d_13_j_) < (len(l))))
                Invariant(((d_24_k_) >= (0)) and ((d_24_k_) <= (len(l))))
                Invariant(Forall(int, lambda d_14_i1_:
                    Forall(int, lambda d_15_j_:
                        Forall(int, lambda d_16_k_:
                            (Implies(((((((((0) <= (d_14_i1_)) and ((d_14_i1_) < (d_6_i_))) and (((0) <= (d_15_j_)) and ((d_15_j_) < (len(l))))) and (((0) <= (d_16_k_)) and ((d_16_k_) < (len(l)))))) or 
                                (d_14_i1_ == d_6_i_ and (d_15_j_) >= 0 and (d_15_j_) < d_13_j_ and (d_16_k_) >= 0 and (d_16_k_) < len(l)) or 
                                (d_14_i1_ == d_6_i_ and (d_15_j_) == d_13_j_ and (d_16_k_) >= 0 and (d_16_k_) < d_24_k_))
                                and ((d_14_i1_) != (d_15_j_)) and ((d_15_j_) != (d_16_k_))) and ((d_14_i1_) != (d_16_k_)), ((((l)[d_14_i1_]) + ((l)[d_15_j_])) + ((l)[d_16_k_])) != (0)), [[(((l)[d_14_i1_]) + ((l)[d_15_j_])) + ((l)[d_16_k_])]])))))
                # invariants-end
                if ((((d_6_i_) != (d_13_j_)) and ((d_13_j_) != (d_24_k_))) and ((d_6_i_) != (d_24_k_))) and (((((l)[d_6_i_]) + ((l)[d_13_j_])) + ((l)[d_24_k_])) == (0)):
                    return True
                d_24_k_ = (d_24_k_) + (1)
            d_13_j_ = (d_13_j_) + (1)
        d_6_i_ = (d_6_i_) + (1)
    return False
    # impl-end
