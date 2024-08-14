from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def below__threshold(l : List[int], t : int) -> bool:
    Requires(Acc(list_pred(l)))
    Ensures(Acc(list_pred(l)))
    Ensures((Result()) == (Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(l)))) or (((l)[d_0_i_]) < (t)))))
    b = False # type : bool
    b = True
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (len(l)):
        Invariant(Acc(list_pred(l)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(l))))
        Invariant((b) == (Forall(int, lambda d_2_i1_:
            not (((d_2_i1_) >= (0)) and ((d_2_i1_) < (d_1_i_))) or (((l)[d_2_i1_]) < (t)))))
        if ((l)[d_1_i_]) >= (t):
            b = False
        d_1_i_ = (d_1_i_) + (1)
    return b