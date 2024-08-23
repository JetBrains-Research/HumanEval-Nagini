from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def NotInArray(a : List[int], x : int) -> bool :
    Requires(Acc(list_pred(a)))
    return Forall(int, lambda d_0_i_:
        (Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len((a)))), ((a)[d_0_i_]) != (x)), [[(a)[d_0_i_]]]))


def common(l1 : List[int], l2 : List[int]) -> List[int]:
    Requires(Acc(list_pred(l2), 1/2))
    Requires(Acc(list_pred(l1), 1/2))
    Ensures(Acc(list_pred(l2), 1/2))
    Ensures(Acc(list_pred(l1), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_4_j_:
        (Implies(((d_4_j_) >= 0 and d_4_j_ < len(l1)), Implies((Exists(int, lambda x: x >= 0 and  x< len(l2) and l2[x] == l1[d_4_j_])), Exists(int, lambda x: x >= 0 and  x< len(Result()) and Result()[x] == l1[d_4_j_]))))))
    # Ensures(Forall(int, lambda d_0_i_:
    #     not ((d_0_i_) >= 0 and d_0_i_ < len(Result())) or ((Exists(int, lambda x : x >= 0 and x < len(l1) and (Result()[d_0_i_]) == (l1[x]))) and 
    #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (Result()[d_0_i_]) == (l2[x]))))))
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
        # Invariant(Forall(int, lambda d_0_i_:
        #     not ((d_0_i_) >= 0 and d_0_i_ < len(c)) or ((Exists(int, lambda x : x >= 0 and x < len(l1) and (c[d_0_i_]) == (l1[x]))) and 
        #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[d_0_i_]) == (l2[x]))))))
        # Invariant(Forall(int, lambda d_0_i_:
        #     (Implies((d_0_i_) >= 0 and d_0_i_ < len(c), (Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[d_0_i_]) == (l1[x]))) and 
        #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[d_0_i_]) == (l2[x])))), [[c[d_0_i_]]])))
        
        d_5_j_ = int(0) # type : int
        d_5_j_ = 0
        # Assume(Forall(int, lambda d_0_i_:
        #     (Implies((d_0_i_) >= 0 and d_0_i_ < len(c), (Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[d_0_i_]) == (l1[x]))) and 
        #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[d_0_i_]) == (l2[x])))), [[c[d_0_i_]]])))
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
            # Invariant(Forall(int, lambda d_0_i_:
            #     (Implies((d_0_i_) >= 0 and d_0_i_ < len(c), ((Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[d_0_i_]) == (l1[x]))) and 
            #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[d_0_i_]) == (l2[x])))) or 
            #         (l1[d_2_i_] == c[d_0_i_] and (Exists(int, lambda x : x >= 0 and x < d_5_j_ and (c[d_0_i_]) == (l2[x]))))), [[c[d_0_i_]]])))
            
            
            # Assume(Forall(int, lambda d_0_i_:
            #     (Implies((d_0_i_) >= 0 and d_0_i_ < len(c), ((Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[d_0_i_]) == (l1[x]))) and 
            #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[d_0_i_]) == (l2[x])))) or 
            #         (l1[d_2_i_] == c[d_0_i_] and (Exists(int, lambda x : x >= 0 and x < d_5_j_ and (c[d_0_i_]) == (l2[x]))))), [[c[d_0_i_]]])))
            # Assume(Forall(int, lambda d_0_i_:
            #     (Implies((d_0_i_) >= 0 and d_0_i_ < len(c), ((Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[d_0_i_]) == (l1[x]))) and 
            #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[d_0_i_]) == (l2[x])))) or 
            #         (l1[d_2_i_] == c[d_0_i_] and (Exists(int, lambda x : x >= 0 and x < d_5_j_ and (c[d_0_i_]) == (l2[x]))))), [[c[d_0_i_]]])))    
            if ((l1)[d_2_i_]) == ((l2)[d_5_j_]) and NotInArray(c, (l1)[d_2_i_]):
                # Assert(Forall(int, lambda d_0_i_:
                #     (Implies((d_0_i_) >= 0 and d_0_i_ < len(c), (Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[d_0_i_]) == (l1[x]))) and 
                #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[d_0_i_]) == (l2[x])))), [[c[d_0_i_]]])))        
                # c_old = list(c)
                # Assert(Forall(int, lambda x: Implies(x >= 0 and x < len(c_old), c_old[x] == c[x])))
                # Assert(Forall(int, lambda d_0_i_:
                #     (Implies((d_0_i_) >= 0 and d_0_i_ < len(c_old), ((Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c_old[d_0_i_]) == (l1[x]))) and 
                #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c_old[d_0_i_]) == (l2[x])))) or 
                #         (l1[d_2_i_] == c[d_0_i_] and (Exists(int, lambda x : x >= 0 and x < d_5_j_ and (c_old[d_0_i_]) == (l2[x]))))), [[c_old[d_0_i_]]])))        
                c = c + [((l1)[d_2_i_])]
                Assert((Exists(int, lambda x : x >= 0 and x < len(l1) and (c[len(c) - 1]) == (l1[x]))))
                Assert((Exists(int, lambda x : x >= 0 and x < len(l2) and (c[len(c) - 1]) == (l2[x]))))
                # Assert(l1[d_2_i_] == c[len(c) - 1] and (Exists(int, lambda x : x >= 0 and x <= d_5_j_ and (c[len(c) - 1]) == (l2[x]))))
                # Assert(((Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[len(c) - 1]) == (l1[x]))) and 
                #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[len(c) - 1]) == (l2[x])))) or 
                #         (l1[d_2_i_] == c[len(c) - 1] and (Exists(int, lambda x : x >= 0 and x <= d_5_j_ and (c[len(c) - 1]) == (l2[x])))))
                # Assert(Forall(int, lambda x: Implies(x >= 0 and x < len(c) - 1, c[x] == Old(c)[x])))
                # Assert(Forall(int, lambda d_0_i_:
                #     (Implies((d_0_i_) >= 0 and d_0_i_ < len(c_old), ((Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c_old[d_0_i_]) == (l1[x]))) and 
                #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c_old[d_0_i_]) == (l2[x])))) or 
                #         (l1[d_2_i_] == c[d_0_i_] and (Exists(int, lambda x : x >= 0 and x < d_5_j_ and (c_old[d_0_i_]) == (l2[x]))))), [[c_old[d_0_i_]]])))        
                # Assert(Forall(int, lambda d_0_i_:
                #     (Implies((d_0_i_) >= 0 and d_0_i_ < len(c) - 1, ((Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[d_0_i_]) == (l1[x]))) and 
                #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[d_0_i_]) == (l2[x])))) or 
                #         (l1[d_2_i_] == c[d_0_i_] and (Exists(int, lambda x : x >= 0 and x < d_5_j_ and (c[d_0_i_]) == (l2[x]))))), [[c[d_0_i_]]])))        
                # Assert(((Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[len(c) - 1]) == (l1[x]))) and 
                #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[len(c) - 1]) == (l2[x])))) or 
                #         (l1[d_2_i_] == c[len(c) - 1] and (Exists(int, lambda x : x >= 0 and x <= d_5_j_ and (c[len(c) - 1]) == (l2[x])))))
                # Assert(Forall(int, lambda d_0_i_:
                #     (Implies(d_0_i_ == len(c) - 1, ((Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[d_0_i_]) == (l1[x]))) and 
                #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[d_0_i_]) == (l2[x])))) or 
                #         (l1[d_2_i_] == c[d_0_i_] and (Exists(int, lambda x : x >= 0 and x < d_5_j_ and (c[d_0_i_]) == (l2[x]))))))))        
                # Assert(Forall(int, lambda d_0_i_:
                #     (Implies((d_0_i_) >= 0 and d_0_i_ < len(c), ((Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[d_0_i_]) == (l1[x]))) and 
                #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[d_0_i_]) == (l2[x])))) or 
                #         (l1[d_2_i_] == c[d_0_i_] and (Exists(int, lambda x : x >= 0 and x <= d_5_j_ and (c[d_0_i_]) == (l2[x]))))), [[c[d_0_i_]]])))
            # Assert(Forall(int, lambda d_0_i_:
            #     (Implies((d_0_i_) >= 0 and d_0_i_ < len(c), ((Exists(int, lambda x : x >= 0 and x < d_2_i_ and (c[d_0_i_]) == (l1[x]))) and 
            #         (Exists(int, lambda x : x >= 0 and x < len(l2) and (c[d_0_i_]) == (l2[x])))) or 
            #         (l1[d_2_i_] == c[d_0_i_] and (Exists(int, lambda x : x >= 0 and x <= d_5_j_ and (c[d_0_i_]) == (l2[x]))))), [[c[d_0_i_]]])))
            d_5_j_ = (d_5_j_) + (1)
        d_2_i_ = (d_2_i_) + (1)
    return c
