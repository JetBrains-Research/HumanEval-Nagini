from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def NotInArray(a : List[int], x : int) -> bool :
    Requires(Acc(list_pred(a)))
    return Forall(int, lambda d_0_i_:
        (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len((a)))), ((a)[d_0_i_]) != (x)), [[(a)[d_0_i_]]]))

@Pure 
def ExistsBoth(a : List[int], b : List[int], x : int) -> bool:
    Requires(Acc(list_pred(a), 1/2))
    Requires(Acc(list_pred(b), 1/2))
    return Exists(int, lambda d_0_i_:
        (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len((a)))), ((a)[d_0_i_]) == (x)))) and Exists(int, lambda d_0_i_:
        (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len((b)))), ((b)[d_0_i_]) == (x))))

def common(l1 : List[int], l2 : List[int]) -> List[int]:
    Requires(Acc(list_pred(l2), 1/2))
    Requires(Acc(list_pred(l1), 1/2))
    Ensures(Acc(list_pred(l2), 1/2))
    Ensures(Acc(list_pred(l1), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_4_j_:
        (Implies(((d_4_j_) >= 0 and d_4_j_ < len(l1)), Implies((Exists(int, lambda x: x >= 0 and  x< len(l2) and l2[x] == l1[d_4_j_])), Exists(int, lambda x: x >= 0 and  x< len(Result()) and Result()[x] == l1[d_4_j_]))))))
    c = list([int(0)] * 0) # type : List[int]
    d_2_i_ = int(0) # type : int
    d_2_i_ = 0
    while (d_2_i_) < (len(l1)):
        Invariant(Acc(list_pred(c)))
        Invariant(Acc(list_pred(l2), 1/2))
        Invariant(Acc(list_pred(l1), 1/2))
        Invariant(((d_2_i_) >= (0)) and ((d_2_i_) <= (len(l1))))
        Invariant(Forall(int, lambda d_4_j_:
            (Implies(((d_4_j_) >= 0 and d_4_j_ < d_2_i_), Implies((Exists(int, lambda x: x >= 0 and  x< len(l2) and l2[x] == l1[d_4_j_])), Exists(int, lambda x: x >= 0 and  x< len(c) and c[x] == l1[d_4_j_]))), 
                [[l1[d_4_j_]]])))
        Invariant(Forall(int, lambda d_0_i_: 
            (Implies((d_0_i_) >= 0 and d_0_i_ < len(c), ExistsBoth(l1, l2, c[d_0_i_])), [[ExistsBoth(l1, l2, c[d_0_i_])]])))
        
        d_5_j_ = int(0) # type : int
        d_5_j_ = 0
        while (d_5_j_) < (len(l2)):
            Invariant(Acc(list_pred(c)))
            Invariant(Acc(list_pred(l2), 1/2))
            Invariant(Acc(list_pred(l1), 1/2))
            Invariant(((d_2_i_) >= (0)) and ((d_2_i_) < (len(l1))))
            Invariant(((d_5_j_) >= (0)) and ((d_5_j_) <= (len(l2))))
            Invariant(Forall(int, lambda d_4_j_:
                (Implies(((d_4_j_) >= 0 and d_4_j_ < d_2_i_), Implies((Exists(int, lambda x: x >= 0 and  x< len(l2) and l2[x] == l1[d_4_j_])), Exists(int, lambda x: x >= 0 and  x< len(c) and c[x] == l1[d_4_j_]))), 
                    [[l1[d_4_j_]]])))
            Invariant(Implies(Exists(int, lambda x: x >= 0 and  x < d_5_j_ and l2[x] == l1[d_2_i_]), Exists(int, lambda x: x >= 0 and  x < len(c) and c[x] == l1[d_2_i_])))
            Invariant(Forall(int, lambda d_0_i_: 
                (Implies((d_0_i_) >= 0 and d_0_i_ < len(c), ExistsBoth(l1, l2, c[d_0_i_])), [[ExistsBoth(l1, l2, c[d_0_i_])]])))
            if ((l1)[d_2_i_]) == ((l2)[d_5_j_]) and NotInArray(c, (l1)[d_2_i_]):
                c = c + [((l1)[d_2_i_])]
                Assert((Exists(int, lambda x : x >= 0 and x < len(l1) and (c[len(c) - 1]) == (l1[x]))))
                Assert((Exists(int, lambda x : x >= 0 and x < len(l2) and (c[len(c) - 1]) == (l2[x]))))
                Assert(ExistsBoth(l1, l2, c[len(c) - 1]))
            d_5_j_ = (d_5_j_) + (1)
        d_2_i_ = (d_2_i_) + (1)
    return c
