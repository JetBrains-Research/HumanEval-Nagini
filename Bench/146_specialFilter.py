from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def first__digit(n : int) -> int :
    Requires(((0) <= (n)))
    Ensures(0 <= Result() and (Result()) < (10))
    if n < 10:
        return n
    else:
        return first__digit(n // 10)

@Pure
def last__digit(n : int) -> int :
    return (n % 10)

def specialFilter(s : List[int]) -> List[int]:
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(Result())))) or (((Result())[d_0_i_]) > (10))))
    Ensures(Forall(int, lambda d_2_i_:
        not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(Result())))) or ((((first__digit((Result())[d_2_i_]) % 2)) == (1)) and (((last__digit((Result())[d_2_i_]) % 2)) == (1)))))
    Ensures(Forall(int, lambda d_5_i_:
        not (((0) <= (d_5_i_)) and ((d_5_i_) < (len(Result())))) or 
            (Exists(int, lambda x: x >= 0 and x < len(s) and s[x] == Result()[d_5_i_]))))
    r = list([int(0)] * 0) # type : List[int]
    d_3_i_ = int(0) # type : int
    d_3_i_ = 0
    r = list([])
    while (d_3_i_) < (len(s)):
        Invariant(Acc(list_pred(r)))
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= (len(s))))
        Invariant(Forall(int, lambda d_5_i_:
            not (((0) <= (d_5_i_)) and ((d_5_i_) < (len(r)))) or (((r)[d_5_i_]) > (10))))
        Invariant(Forall(int, lambda d_7_i_:
            (not (((0) <= (d_7_i_)) and ((d_7_i_) < (len(r)))) or ((((first__digit((r)[d_7_i_]) % 2)) == (1)) and (((last__digit((r)[d_7_i_]) % 2)) == (1))), [[first__digit((r)[d_7_i_])]])))
        Invariant(Forall(int, lambda d_5_i_:
            not (((0) <= (d_5_i_)) and ((d_5_i_) < (len(r)))) or 
                (Exists(int, lambda x: x >= 0 and x < len(s) and s[x] == r[d_5_i_]))))
        if ((((s)[d_3_i_]) > (10)) and (((last__digit((s)[d_3_i_]) % 2)) == (1))) and (((first__digit((s)[d_3_i_]) % 2)) == (1)):
            r = (r) + [(s)[d_3_i_]]
        d_3_i_ = (d_3_i_) + (1)
    return r
