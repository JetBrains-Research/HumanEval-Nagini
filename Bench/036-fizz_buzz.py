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
    result : int = 0
    i : int = 0
    while (i) < (n):
        # invariants-start
        Invariant(((0) <= (i)) and ((i) <= (n)))
        Invariant(Forall(int, lambda x : (Implies(x >= 0 and x < n, 
            fizz_buzz_fun(x + 1) == (count7__r(x) if ((x % 11 == 0) or (x % 13 == 0)) else 0) + fizz_buzz_fun(x)), [[fizz_buzz_fun(x + 1)]])))
        Invariant(result == fizz_buzz_fun(i))
        # invariants-end
        if (((i % 11)) == (0)) or (((i % 13)) == (0)):
            cnt : int = count7(i)
            result = (result) + (cnt)
        i = (i) + (1)
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

    # pure-start
    if n == 0:
        return 0
    else:
        return (count7__r(n - 1) if ((n - 1) % 11 == 0 or (n - 1) % 13 == 0) else 0) + fizz_buzz_fun(n - 1)
    # pure-end


def count7(x : int) -> int:
    # pre-conditions-start
    Requires(x >= 0)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() >= 0)
    Ensures((Result()) == (count7__r(x)))
    # post-conditions-end

    # impl-start
    count : int = 0
    y : int = x
    while (y) > (0):
        # invariants-start
        Invariant(((0) <= (y)) and ((y) <= (x)))
        Invariant(((count) + (count7__r(y))) == (count7__r(x)))
        # invariants-end
        if ((y % 10)) == (7):
            count = (count) + (1)
        y = y // 10
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

    # pure-start
    if x == 0:
        return 0
    else:
        return (x % 10 == 7) + count7__r(x // 10)
    # pure-end
