from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def fizz__buzz(n : int) -> int:
    Requires(n >= 0)
    Ensures(Result() >= 0)
    Ensures((Result()) == fizz_buzz_fun(n))
    result = int(0) # type : int
    result = 0
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < (n):
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (n)))
        Invariant(Forall(int, lambda x : (Implies(x >= 0 and x < n, 
            fizz_buzz_fun(x + 1) == (count7__r(x) if ((x % 11 == 0) or (x % 13 == 0)) else 0) + fizz_buzz_fun(x)), [[fizz_buzz_fun(x + 1)]])))
        Invariant(result == fizz_buzz_fun(d_1_i_))
        if (((d_1_i_ % 11)) == (0)) or (((d_1_i_ % 13)) == (0)):
            d_4_cnt_ = int(0) # type : int
            d_4_cnt_ = count7(d_1_i_)
            result = (result) + (d_4_cnt_)
        d_1_i_ = (d_1_i_) + (1)
    return result

@Pure 
def fizz_buzz_fun(n : int) -> int:
    Requires(n >= 0)
    Ensures(Result() >= 0)
    if n == 0:
        return 0
    else:
        return (count7__r(n - 1) if ((n - 1) % 11 == 0 or (n - 1) % 13 == 0) else 0) + fizz_buzz_fun(n - 1)


def count7(x : int) -> int:
    Requires(x >= 0)
    Ensures(Result() >= 0)
    Ensures((Result()) == (count7__r(x)))
    count = int(0) # type : int
    count = 0
    d_6_y_ = int(0) # type : int
    d_6_y_ = x
    while (d_6_y_) > (0):
        Invariant(((0) <= (d_6_y_)) and ((d_6_y_) <= (x)))
        Invariant(((count) + (count7__r(d_6_y_))) == (count7__r(x)))
        if ((d_6_y_ % 10)) == (7):
            count = (count) + (1)
        d_6_y_ = d_6_y_ // 10
    return count

@Pure
def count7__r(x : int) -> int :
    Requires(x >= 0)
    Ensures(Result() >= 0)
    if x == 0:
        return 0
    else:
        return (x % 10 == 7) + count7__r(x // 10)
