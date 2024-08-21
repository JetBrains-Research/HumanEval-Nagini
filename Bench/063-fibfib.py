from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def fibfib(n : int) -> int :
    Requires((n) >= (0))
    Ensures((Result()) >= (0))
    if ((n) == (0)) or ((n) == (1)):
        return 0
    elif (n) == (2):
        return 1
    elif True:
        return ((fibfib((n) - (1))) + (fibfib((n) - (2)))) + (fibfib((n) - (3)))

def ComputeFibFib(n : int) -> int:
    Requires((n) >= (0))
    Ensures((Result()) >= (0))
    Ensures((Result()) == (fibfib(n)))
    result = int(0) # type : int
    if ((n) == (0)) or ((n) == (1)):
        result = 0
        return result
    if (n) == (2):
        result = 1
        return result
    d_0_a_ = int(0) # type : int
    d_1_b_ = int(0) # type : int
    d_2_c_ = int(0) # type : int
    rhs0_ = 0 # type : int
    rhs1_ = 0 # type : int
    rhs2_ = 1 # type : int
    d_0_a_ = rhs0_
    d_1_b_ = rhs1_
    d_2_c_ = rhs2_
    d_3_i_ = int(0) # type : int
    d_3_i_ = 3
    while (d_3_i_) <= (n):
        Invariant(((3) <= (d_3_i_)) and ((d_3_i_) <= ((n) + (1))))
        Invariant((d_0_a_) == (fibfib((d_3_i_) - (3))))
        Invariant((d_1_b_) == (fibfib((d_3_i_) - (2))))
        Invariant((d_2_c_) == (fibfib((d_3_i_) - (1))))
        d_4_temp_ = int(0) # type : int
        d_4_temp_ = ((d_2_c_) + (d_1_b_)) + (d_0_a_)
        d_0_a_ = d_1_b_
        d_1_b_ = d_2_c_
        d_2_c_ = d_4_temp_
        d_3_i_ = (d_3_i_) + (1)
    result = d_2_c_
    return result
