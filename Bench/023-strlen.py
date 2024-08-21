from nagini_contracts.contracts import *

def strlen(s : str) -> int: 
    Ensures((Result()) == (len(s)))
    return len(s) 