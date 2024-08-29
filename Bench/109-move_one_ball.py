from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def is__sorted(a : List[int], l : int, r : int) -> bool :
    Requires(Acc(list_pred(a)))
    Requires(((0) <= (l)) and ((l) <= (r)) and ((r) <= (len(a))))
    return Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            not ((((l) <= (d_0_i_)) and ((d_0_i_) < (d_1_j_))) and ((d_1_j_) < (r))) or (((a)[d_0_i_]) <= ((a)[d_1_j_]))))

def move__one__ball(a : List[int]) -> bool:
    Requires(Acc(list_pred(a)))
    Requires((len(a)) > (0))
    Requires(Forall(int, lambda d_2_i_:
        Forall(int, lambda d_3_j_:
            not (((((0) <= (d_2_i_)) and ((d_2_i_) < (len(a)))) and (((0) <= (d_3_j_)) and ((d_3_j_) < (len(a))))) and ((d_2_i_) != (d_3_j_))) or (((a)[d_2_i_]) != ((a)[d_3_j_])))))
    Ensures(Acc(list_pred(a)))
    Ensures(Forall(int, lambda d_2_i_:
        Forall(int, lambda d_3_j_:
            not (((((0) <= (d_2_i_)) and ((d_2_i_) < (len(a)))) and (((0) <= (d_3_j_)) and ((d_3_j_) < (len(a))))) and ((d_2_i_) != (d_3_j_))) or (((a)[d_2_i_]) != ((a)[d_3_j_])))))
    Ensures(Implies(Result(), Exists(int, lambda d_4_i_:
        (((0) <= (d_4_i_)) and ((d_4_i_) < (len(a)))) and (is__sorted(a, 0, d_4_i_) and is__sorted(a, d_4_i_, len(a)) and (Forall(int, lambda d_5_j_:
            Implies(0 <= d_5_j_ and d_5_j_ < d_4_i_, 
                Forall(int, lambda d_6_j_:
                    Implies(d_4_i_ <= d_6_j_ and d_6_j_ < len(a), a[d_5_j_] > a[d_6_j_])))))))))
    Ensures(Implies(Exists(int, lambda d_4_i_:
        (((0) <= (d_4_i_)) and ((d_4_i_) < (len(a)))) and (is__sorted(a, 0, d_4_i_) and is__sorted(a, d_4_i_, len(a)) and (Forall(int, lambda d_5_j_:
            Implies(0 <= d_5_j_ and d_5_j_ < d_4_i_, 
                Forall(int, lambda d_6_j_:
                    Implies(d_4_i_ <= d_6_j_ and d_6_j_ < len(a), a[d_5_j_] > a[d_6_j_]))))))), Result()))
    can = False # type : bool
    if (len(a)) <= (1):
        Assert(is__sorted(a, 0, len(a)))
        can = True
        return can
    can = False
    d_5_i_ = int(0) # type : int
    d_5_i_ = 0
    d_6_min__index_ = int(0) # type : int
    d_6_min__index_ = 0
    while (d_5_i_) < (len(a)):
        Invariant(Acc(list_pred(a)))
        Invariant(((0) <= (d_5_i_)) and ((d_5_i_) <= (len(a))))
        Invariant(((0) <= (d_6_min__index_)) and ((d_6_min__index_) < (len(a))))
        Invariant(Forall(int, lambda d_2_i_:
            (Forall(int, lambda d_3_j_:
                (not (((((0) <= (d_2_i_)) and ((d_2_i_) < (len(a)))) and (((0) <= (d_3_j_)) and ((d_3_j_) < (len(a))))) and ((d_2_i_) != (d_3_j_))) or (((a)[d_2_i_]) != ((a)[d_3_j_]))
                 , [[(a)[d_3_j_]]]))
                , [[a[d_2_i_]]])))
        Invariant(Forall(int, lambda d_7_j_:
            (not ((((0) <= (d_7_j_)) and ((d_7_j_) < (d_5_i_))) and ((d_6_min__index_) != (d_7_j_))) or (((a)[d_6_min__index_]) < ((a)[d_7_j_])), [[(a)[d_7_j_]]])))
        if ((a)[d_5_i_]) < ((a)[d_6_min__index_]):
            d_6_min__index_ = d_5_i_
        d_5_i_ = (d_5_i_) + (1)

    Assert(Implies(is__sorted(a, 0, d_6_min__index_) and is__sorted(a, d_6_min__index_, len(a)) and d_6_min__index_ == 0, 
        is__sorted(a, 0, len(a))))
    Assert(Implies(is__sorted(a, 0, d_6_min__index_) and is__sorted(a, d_6_min__index_, len(a)) and d_6_min__index_ != 0 and a[len(a) - 1] < a[0], 
        (Forall(int, lambda d_5_j_:
            Implies(0 <= d_5_j_ and d_5_j_ < d_6_min__index_, 
                Forall(int, lambda d_6_j_:
                    Implies(d_6_min__index_ <= d_6_j_ and d_6_j_ < len(a), a[d_5_j_] > a[d_6_j_])))))))
    can = is__sorted(a, 0, d_6_min__index_) and is__sorted(a, d_6_min__index_, len(a)) and (d_6_min__index_ == 0 or a[len(a) - 1] < a[0])
    return can
