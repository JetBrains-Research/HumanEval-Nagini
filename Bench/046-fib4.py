from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def fib4__rec(n : int) -> int :
    # pre-conditions-start
    Requires(n >= 0)
    # pre-conditions-end

    # impl-start
    if (((n) == (0)) or ((n) == (1))) or ((n) == (2)):
        return 0
    elif (n) == (3):
        return 1
    elif True:
        return (((fib4__rec((n) - (1))) + (fib4__rec((n) - (2)))) + (fib4__rec((n) - (3)))) + (fib4__rec((n) - (4)))
    # impl-end

def fib4(n : int) -> int:
    # pre-conditions-start
    Requires(n >= 0)
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) == (fib4__rec(n)))
    # post-conditions-end

    # impl-start
    if (((n) == (0)) or ((n) == (1))) or ((n) == (2)):
        return 0
    if (n) == (3):
        return 1
    d_0_a_ : int = 0
    d_1_b_ : int = 0
    d_2_c_ : int = 0
    d_3_d_ : int = 1
    d_4_i_ : int = 4
    while (d_4_i_) <= (n):
        # invariants-start
        Invariant(((4) <= (d_4_i_)) and ((d_4_i_) <= ((n) + (1))))
        Invariant((d_0_a_) == (fib4__rec((d_4_i_) - (4))))
        Invariant((d_1_b_) == (fib4__rec((d_4_i_) - (3))))
        Invariant((d_2_c_) == (fib4__rec((d_4_i_) - (2))))
        Invariant((d_3_d_) == (fib4__rec((d_4_i_) - (1))))
        # invariants-end
        d_5_temp_ : int = (((d_3_d_) + (d_2_c_)) + (d_1_b_)) + (d_0_a_)
        d_0_a_ = d_1_b_
        d_1_b_ = d_2_c_
        d_2_c_ = d_3_d_
        d_3_d_ = d_5_temp_
        d_4_i_ = (d_4_i_) + (1)
    result : int = d_3_d_
    return result
    # impl-end
