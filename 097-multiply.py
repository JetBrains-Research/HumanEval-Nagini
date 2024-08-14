from nagini_contracts.contracts import *

@Pure
def last__digit(n : int) -> int :
    if (n) < (0):
        return (((0) - (n)) % 10)
    elif True:
        return (n % 10)

def multiply(a : int, b : int) -> int:
    Requires((a) >= (0))
    Requires((b) >= (0))
    Ensures((Result()) == ((last__digit(a)) * (last__digit(b))))
    c = int(0) # type : int
    c = (last__digit(a)) * (last__digit(b))
    return c
