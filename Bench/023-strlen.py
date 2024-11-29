from nagini_contracts.contracts import *

def strlen(s : str) -> int: 
    # pre-conditions-start
    Ensures((ResultT(int)) == (len(s)))
    # pre-conditions-end

    # impl-start
    return len(s) 
    # impl-end
