from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def last__digit(n : int) -> int :
    # pure-start
    if (n) < (0):
        return (((0) - (n)) % 10)
    elif True:
        return (n % 10)
    # pure-end

def multiply(a : int, b : int) -> int:
    # pre-conditions-start
    Requires((a) >= (0))
    Requires((b) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) == ((last__digit(a)) * (last__digit(b))))
    # post-conditions-end

    # impl-start
    return (last__digit(a)) * (last__digit(b))
    # impl-end
