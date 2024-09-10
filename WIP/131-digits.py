from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *


@Pure 
def count_odd(n : int) -> int:
    Requires((n) >= (0))
    if n == 0:
        return 0
    else:
        return (1 if (n % 10) % 2 == 1 else 0) + count_odd(n // 10)

def digits(n : int) -> int:
    Requires((n) >= (0))
    Ensures(Result() >= 0)
    # Ensures((Result() == 0) == (count_odd(n) == 0))
    odd_count = 0
    product = 1
    n_copy = n
    s1 = 0 
    pw1 = 1
    while n > 0:
        Invariant(n >= 0)
        Invariant(odd_count >= 0)
        Invariant(product >= 1)
        Invariant(pw1 >= 1)
        Invariant(s1 >= 0)
        Invariant(odd_count == count_odd(s1))
        if n % 2 == 1:
            odd_count += 1
            product = product * (n % 10)
        Assert(count_odd(s1 + (n % 10) * pw1) == (1 if (n % 10) % 2 == 1 else 0) + count_odd(s1))
        s1 = s1 + (n % 10) * pw1
        pw1 = pw1 * 10
        # Assert(count_odd(n_copy, n // 10) == (1 if n % 2 == 1 else 0) + count_odd(n_copy, n))
        n //= 10
    # Assert(odd_count == count_odd(n_copy))
    if odd_count == 0:
        return 0
    return product