from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def fizz__buzz(n : int) -> int:
    # pre-conditions-start
    Requires(n >= 0)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() >= 0)
    Ensures((Result()) == fizz_buzz_fun(n))
    # post-conditions-end

    # impl-start
    result = int(0) # type : int
    result = 0
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (n):
        # invariants-start
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (n)))
        Invariant(Forall(int, lambda x : (Implies(x >= 0 and x < n, 
            fizz_buzz_fun(x + 1) == (count7__r(x) if ((x % 11 == 0) or (x % 13 == 0)) else 0) + fizz_buzz_fun(x)), [[fizz_buzz_fun(x + 1)]])))
        Invariant(result == fizz_buzz_fun(d_1_i_))
        # invariants-end
        if (((d_1_i_ % 11)) == (0)) or (((d_1_i_ % 13)) == (0)):
            d_4_cnt_ = int(0) # type : int
            d_4_cnt_ = count7(d_1_i_)
            result = (result) + (d_4_cnt_)
        d_1_i_ = (d_1_i_) + (1)
    return result
    # impl-end

@Pure 
def fizz_buzz_fun(n : int) -> int:
    # pre-conditions-start
    Requires(n >= 0)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() >= 0)
    # post-conditions-end

    # impl-start
    if n == 0:
        return 0
    else:
        return (count7__r(n - 1) if ((n - 1) % 11 == 0 or (n - 1) % 13 == 0) else 0) + fizz_buzz_fun(n - 1)
    # impl-end


def count7(x : int) -> int:
    # pre-conditions-start
    Requires(x >= 0)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() >= 0)
    Ensures((Result()) == (count7__r(x)))
    # post-conditions-end

    # impl-start
    count = int(0) # type : int
    count = 0
    d_6_y_ = int(0) # type : int
    d_6_y_ = x
    while (d_6_y_) > (0):
        # invariants-start
        Invariant(((0) <= (d_6_y_)) and ((d_6_y_) <= (x)))
        Invariant(((count) + (count7__r(d_6_y_))) == (count7__r(x)))
        # invariants-end
        if ((d_6_y_ % 10)) == (7):
            count = (count) + (1)
        d_6_y_ = d_6_y_ // 10
    return count
    # impl-end  

@Pure
def count7__r(x : int) -> int :
    # pre-conditions-start
    Requires(x >= 0)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() >= 0)
    # post-conditions-end

    # impl-start
    if x == 0:
        return 0
    else:
        return (x % 10 == 7) + count7__r(x // 10)
    # impl-end
