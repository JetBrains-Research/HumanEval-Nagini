from nagini_contracts.contracts import *

def any__int(a : int, b : int, c : int) -> bool:
    Ensures((Result()) == ((((a) == ((b) + (c))) or ((b) == ((a) + (c)))) or ((c) == ((a) + (b)))))
    r = False # type : bool
    r = (((a) == ((b) + (c))) or ((b) == ((a) + (c)))) or ((c) == ((a) + (b)))
    return r