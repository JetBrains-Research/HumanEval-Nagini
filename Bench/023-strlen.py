from nagini_contracts.contracts import *

def strlen(s : str) -> int: 
    Ensures((ResultT(int)) == (len(s)))
    return len(s) 