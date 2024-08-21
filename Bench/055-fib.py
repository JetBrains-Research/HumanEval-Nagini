from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def fib(n : int) -> int :
    Requires((n) >= (0))
    Ensures(Result() >= 0)
    if (n) == (0):
        return 0
    elif (n) == (1):
        return 1
    elif True:
        return (fib((n) - (1))) + (fib((n) - (2)))

def ComputeFib(n : int) -> int:
    Requires((n) >= (0))
    Ensures((Result()) == (fib(n)))
    Ensures(Result() >= 0)
    result = int(0) # type : int
    if (n) == (0):
        result = 0
        return result
    if (n) == (1):
        result = 1
        return result
    d_0_a_ = int(0) # type : int
    d_1_b_ = int(0) # type : int
    rhs0_ = 0 # type : int
    rhs1_ = 1 # type : int
    d_0_a_ = rhs0_
    d_1_b_ = rhs1_
    d_2_i_ = int(0) # type : int
    d_2_i_ = 2
    while (d_2_i_) <= (n):
        Invariant(((2) <= (d_2_i_)) and ((d_2_i_) <= ((n) + (1))))
        Invariant((d_0_a_) == (fib((d_2_i_) - (2))))
        Invariant((d_1_b_) == (fib((d_2_i_) - (1))))
        d_3_temp_ = int(0) # type : int
        d_3_temp_ = (d_0_a_) + (d_1_b_)
        d_0_a_ = d_1_b_
        d_1_b_ = d_3_temp_
        d_2_i_ = (d_2_i_) + (1)
    result = d_1_b_
    return result