from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def choose__num(x : int, y : int) -> int:
    # pre-conditions-start
    Requires(((0) <= (x)) and ((0) <= (y)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(((Result()) == (-1)) or (((Result()) >= (x)) and ((Result()) <= (y))))
    Ensures(((Result()) == (-1)) or (((Result() % 2)) == (0)))
    Ensures(((Result()) == (-1)) or (Forall(int, lambda d_0_i_:
        not ((((x) <= (d_0_i_)) and ((d_0_i_) <= (y))) and (((d_0_i_ % 2)) == (0))) or ((Result()) >= (d_0_i_)))))
    Ensures(((Result()) == (-1)) == ((x) >= (y)))
    # post-conditions-end

    # impl-start
    num = int(0) # type : int
    num = -1
    if (x) >= (y):
        return num
    if ((x % 2)) == (0):
        num = x
    elif True:
        num = (x) + (1)
    d_1_i_ = int(0) # type : int
    d_1_i_ = (x) + (2)
    while (d_1_i_) <= (y):
        # invariants-start
        Invariant(((d_1_i_) >= (x)) and ((d_1_i_) <= ((y) + (1))))
        Invariant(((num) == (-1)) or (((num % 2)) == (0)))
        Invariant(Forall(int, lambda d_2_j_:
            not ((((x) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_))) and (((d_2_j_ % 2)) == (0))) or ((num) >= (d_2_j_))))
        Invariant(((num) == (-1)) or (((num) >= (x)) and ((num) < (d_1_i_))))
        # invariants-end
        if ((d_1_i_ % 2)) == (0):
            num = d_1_i_
        d_1_i_ = (d_1_i_) + (1)
    return num
    # impl-end
