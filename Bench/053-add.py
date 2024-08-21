from nagini_contracts.contracts import *

def add(x : int, y : int) -> int:
    Ensures((Result()) == ((x) + (y)))
    z = int(0) # type : int
    z = (x) + (y)
    return z