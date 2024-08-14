from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def CountNumbersStartingOrEndingWithOne(n : int) -> int:
    Requires((n) > (0))
    Ensures(not ((n) == (1)) or ((Result()) == (1)))
    Ensures(not ((n) > (1)) or ((Result()) == ((18) * (Pow(10, (n) - (2))))))
    count = int(0) # type : int
    if (n) == (1):
        count = 1
    elif True:
        count = (18) * (Pow(10, (n) - (2)))
    return count

@Pure
def Pow(base : int, exponent : int) -> int :
    Requires((exponent) >= (0))
    if (exponent) == (0):
        return 1
    else:
        return (base) * (Pow(base, (exponent) - (1)))