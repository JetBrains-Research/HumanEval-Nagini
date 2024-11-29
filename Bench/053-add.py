from nagini_contracts.contracts import *

def add(x : int, y : int) -> int:
    # pre-conditions-start
    Ensures((Result()) == ((x) + (y)))
    # pre-conditions-end

    # impl-start
    z : int = (x) + (y)
    return z
    # impl-end
