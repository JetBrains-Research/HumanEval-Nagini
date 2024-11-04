from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def fibfib(n : int) -> int :
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) >= (0))
    # post-conditions-end

    # impl-start
    if ((n) == (0)) or ((n) == (1)):
        return 0
    elif (n) == (2):
        return 1
    elif True:
        return ((fibfib((n) - (1))) + (fibfib((n) - (2)))) + (fibfib((n) - (3)))
    # impl-end

def ComputeFibFib(n : int) -> int:
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) >= (0))
    Ensures((Result()) == (fibfib(n)))
    # post-conditions-end

    # impl-start
    if ((n) == (0)) or ((n) == (1)):
        return 0
    if (n) == (2):
        return 1
    d_0_a_ : int = 0
    d_1_b_ : int = 0
    d_2_c_ : int = 1
    d_3_i_ : int = 3
    while (d_3_i_) <= (n):
        # invariants-start
        Invariant(((3) <= (d_3_i_)) and ((d_3_i_) <= ((n) + (1))))
        Invariant((d_0_a_) == (fibfib((d_3_i_) - (3))))
        Invariant((d_1_b_) == (fibfib((d_3_i_) - (2))))
        Invariant((d_2_c_) == (fibfib((d_3_i_) - (1))))
        # invariants-end
        d_4_temp_ : int = ((d_2_c_) + (d_1_b_)) + (d_0_a_)
        d_0_a_ = d_1_b_
        d_1_b_ = d_2_c_
        d_2_c_ = d_4_temp_
        d_3_i_ = (d_3_i_) + (1)
    result : int = d_2_c_
    return result
    # impl-end
