from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def CountNumbersStartingOrEndingWithOne(n : int) -> int:
    # pre-conditions-start
    Requires((n) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(not ((n) == (1)) or ((Result()) == (1)))
    Ensures(not ((n) > (1)) or ((Result()) == ((18) * (Pow(10, (n) - (2))))))
    # post-conditions-end

    # impl-start
    count : int = int(0)
    if (n) == (1):
        count = 1
    elif True:
        count = (18) * (Pow(10, (n) - (2)))
    return count
    # impl-end

@Pure
def Pow(base : int, exponent : int) -> int :
    # pre-conditions-start
    Requires((exponent) >= (0))
    # pre-conditions-end

    # impl-start
    if (exponent) == (0):
        return 1
    else:
        return (base) * (Pow(base, (exponent) - (1)))
    # impl-end