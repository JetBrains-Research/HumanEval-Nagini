from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def greatest_common_divisor(a: int, b: int) -> int:
    # pre-conditions-start
    Requires(a != 0 or b != 0)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() != 0)
    # post-conditions-end

    # impl-start
    x = a
    y = b

    while y != 0:
        # invariants-start
        Invariant(x != 0 or y != 0)
        # invariants-end
        temp = y
        y = x % y
        x = temp

    return x
    # impl-end
