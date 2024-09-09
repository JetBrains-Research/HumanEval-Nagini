from nagini_contracts.contracts import *

def add(x : int, y : int) -> int:
    # pre-conditions-start
    Ensures((Result()) == ((x) + (y)))
    # pre-conditions-end

    # impl-start
    z = int(0) # type : int
    z = (x) + (y)
    return z
    # impl-end