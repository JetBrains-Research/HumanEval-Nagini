from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def rot__sym(c : int) -> int :
    Requires(c >= 0 and c <= 25)
    Ensures(Result() >= 0 and Result() <= 25)
    d_0_alph_ = c - 0 # type : int
    return ((d_0_alph_) + ((2) * (2))) % 26

def encrypt(s : List[int]) -> List[int]:
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) or (((0) <= ((s)[d_1_i_])) and (((s)[d_1_i_]) <= (25)))))
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (len(s)))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) or (((0) <= ((s)[d_1_i_])) and (((s)[d_1_i_]) <= (25)))))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(Result())))) or (((0) <= ((Result())[d_1_i_])) and (((Result())[d_1_i_]) <= (25)))))
    Ensures(Forall(int, lambda d_2_i_:
        not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(s)))) or (((Result())[d_2_i_]) == (rot__sym((s)[d_2_i_])))))
    r : List[int] = [] # type : List[int]
    d_3_i_ = int(0) # type : int
    d_3_i_ = 0
    while (d_3_i_) < (len(s)):
        Invariant(Acc(list_pred(s)))
        Invariant(Acc(list_pred(r)))
        Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= (len(s))))
        Invariant((len(r)) == (d_3_i_))
        Invariant(Forall(int, lambda d_1_i_:
            not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) or (((0) <= ((s)[d_1_i_])) and (((s)[d_1_i_]) <= (25)))))    
        Invariant(Forall(int, lambda d_1_i_:
            not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(r)))) or (((0) <= ((r)[d_1_i_])) and (((r)[d_1_i_]) <= (25)))))  
        Invariant(Forall(int, lambda d_4_j_:
            not (((0) <= (d_4_j_)) and ((d_4_j_) < (d_3_i_))) or (((r)[d_4_j_]) == (rot__sym((s)[d_4_j_])))))
        r = (r) + [rot__sym((s)[d_3_i_])]
        d_3_i_ = (d_3_i_) + (1)
    return r