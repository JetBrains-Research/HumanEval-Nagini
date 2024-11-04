from nagini_contracts.contracts import *

def any__int(a : int, b : int, c : int) -> bool:
    # post-conditions-start
    Ensures((Result()) == ((((a) == ((b) + (c))) or ((b) == ((a) + (c)))) or ((c) == ((a) + (b)))))
    # post-conditions-end

    # impl-start
    return (((a) == ((b) + (c))) or ((b) == ((a) + (c)))) or ((c) == ((a) + (b)))
    # impl-end