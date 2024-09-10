from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def factorial(n : int) -> int :
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) >= (0))
    # post-conditions-end

    # impl-start
    if (n) == (0):
        return 1
    else:
        return (n) * (factorial((n) - (1)))
    # impl-end

@Pure
def special__factorial__rec(n : int) -> int :
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) >= (0))
    # post-conditions-end

    # impl-start
    if (n) == (0):
        return 1
    else:
        return factorial(n) * (special__factorial__rec((n) - (1)))
    # impl-end

def special__factorial(n : int) -> int:
    # pre-conditions-start
    Requires((n) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) == (special__factorial__rec(n)))
    # post-conditions-end

    # impl-start
    result = int(0) # type : int
    result = 1
    d_2_fact_ = int(0) # type : int
    d_2_fact_ = 1
    d_3_i_ = int(0) # type : int
    d_3_i_ = 1
    while (d_3_i_) <= (n):
        # invariants-start
        Invariant(((1) <= (d_3_i_)) and ((d_3_i_) <= (n + 1)))
        Invariant(Forall(int, lambda d_2_i_: (not (((0) <= (d_2_i_)) and ((d_2_i_) <= (n))) or ((factorial(d_2_i_ + 1)) == (factorial(d_2_i_) * (d_2_i_ + 1))), [[factorial(d_2_i_ + 1)]])))
        Invariant(Forall(int, lambda d_2_i_: (not (((0) <= (d_2_i_)) and ((d_2_i_) <= (n))) or ((special__factorial__rec(d_2_i_ + 1)) == (special__factorial__rec(d_2_i_) * factorial(d_2_i_ + 1))), [[special__factorial__rec(d_2_i_ + 1)]])))
        Invariant((result) == (special__factorial__rec(d_3_i_ - 1)))
        Invariant((d_2_fact_) == (factorial(d_3_i_ - 1)))
        # invariants-end
        d_2_fact_ = (d_2_fact_) * (d_3_i_)
        result = (result) * (d_2_fact_)
        d_3_i_ = (d_3_i_) + (1)
    return result
    # impl-end
