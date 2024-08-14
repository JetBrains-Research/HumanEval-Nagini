from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def factorial__spec(n : int) -> int :
    Requires(n >= -1)
    Ensures(Result() >= 0)
    if n == -1:
        return 1
    else:
        return (n + 1) * factorial__spec(n - 1)

@Pure
def sum__spec(n : int) -> int :
    Requires(n >= -1)
    Ensures(Result() >= 0)
    if 0 > n:
        return 0
    else:
        return n + 1 + sum__spec(n - 1)

def f(n : int) -> List[int]:
    Requires((n) >= (1))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (n))
    Ensures(Forall(int, lambda d_2_i_:
        not ((((d_2_i_) >= (0)) and ((d_2_i_) < (len(Result())))) and (((d_2_i_ % 2)) == (0))) or (((Result())[d_2_i_]) == (factorial__spec(d_2_i_ - 1)))))
    Ensures(Forall(int, lambda d_3_i_:
        not ((((d_3_i_) >= (0)) and ((d_3_i_) < (len(Result())))) and (((d_3_i_ % 2)) != (0))) or (((Result())[d_3_i_]) == (sum__spec(d_3_i_ - 1)))))
    result = list([int(0)] * 0) # type : List[int]
    result = list([])
    d_4_i_ = int(0) # type : int
    d_4_i_ = 0
    while (d_4_i_) < (n):
        Invariant(Acc(list_pred(result)))
        Invariant(((d_4_i_) >= (0)) and ((d_4_i_) <= (n)))
        Invariant((len(result)) == (d_4_i_))
        Invariant(Forall(int, lambda d_5_i_:
            (Implies((((d_5_i_) >= (0)) and ((d_5_i_) < (len(result)))) and (((d_5_i_ % 2)) == (0)), ((result)[d_5_i_]) == (factorial__spec(d_5_i_ - 1))), [[factorial__spec(d_5_i_ - 1)]])))
        Invariant(Forall(int, lambda d_6_i_:
            (Implies((((d_6_i_) >= (0)) and ((d_6_i_) < (len(result)))) and (((d_6_i_ % 2)) != (0)), ((result)[d_6_i_]) == (sum__spec(d_6_i_ - 1))), [[sum__spec(d_6_i_ - 1)]])))
        if ((d_4_i_ % 2)) == (0):
            d_7_x_ = int(0) # type : int
            d_7_x_ = 1
            d_8_j_ = int(0) # type : int
            d_8_j_ = 0
            while (d_8_j_) < (d_4_i_):
                Invariant(Acc(list_pred(result)))
                Invariant(((d_4_i_) >= (0)) and ((d_4_i_) <= (n)))
                Invariant((len(result)) == (d_4_i_))
                Invariant(((d_8_j_) >= (0)) and ((d_8_j_) <= (d_4_i_)))
                Invariant((d_7_x_) == (factorial__spec(d_8_j_ - 1)))
                Invariant(Forall(int, lambda d_5_i_:
                    (Implies((((d_5_i_) >= (0)) and ((d_5_i_) < (len(result)))) and (((d_5_i_ % 2)) == (0)), ((result)[d_5_i_]) == (factorial__spec(d_5_i_ - 1))), [[factorial__spec(d_5_i_ - 1)]])))
                Invariant(Forall(int, lambda d_6_i_:
                    (Implies((((d_6_i_) >= (0)) and ((d_6_i_) < (len(result)))) and (((d_6_i_ % 2)) != (0)), ((result)[d_6_i_]) == (sum__spec(d_6_i_ - 1))), [[sum__spec(d_6_i_ - 1)]])))
                d_7_x_ = (d_7_x_) * (d_8_j_ + 1)
                d_8_j_ = (d_8_j_) + (1)
            result = (result) + [d_7_x_]
        else:
            d_9_x_ = int(0) # type : int
            d_9_x_ = 0
            d_10_j_ = int(0) # type : int
            d_10_j_ = 0
            while (d_10_j_) < (d_4_i_):
                Invariant(Acc(list_pred(result)))
                Invariant(((d_4_i_) >= (0)) and ((d_4_i_) <= (n)))
                Invariant((len(result)) == (d_4_i_))
                Invariant(((d_10_j_) >= (0)) and ((d_10_j_) <= (d_4_i_)))
                Invariant((d_9_x_) == (sum__spec(d_10_j_ - 1)))
                Invariant(Forall(int, lambda d_5_i_:
                    (Implies((((d_5_i_) >= (0)) and ((d_5_i_) < (len(result)))) and (((d_5_i_ % 2)) == (0)), ((result)[d_5_i_]) == (factorial__spec(d_5_i_ - 1))), [[factorial__spec(d_5_i_ - 1)]])))
                Invariant(Forall(int, lambda d_6_i_:
                    (Implies((((d_6_i_) >= (0)) and ((d_6_i_) < (len(result)))) and (((d_6_i_ % 2)) != (0)), ((result)[d_6_i_]) == (sum__spec(d_6_i_ - 1))), [[sum__spec(d_6_i_ - 1)]])))
                d_9_x_ = (d_9_x_) + (d_10_j_ + 1)
                d_10_j_ = (d_10_j_) + (1)
            result = (result) + [d_9_x_]
        d_4_i_ = (d_4_i_) + (1)
    return result
