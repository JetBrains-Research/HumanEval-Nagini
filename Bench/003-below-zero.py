from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pure-pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return (s)[j - 1] + (psum(i, j - 1, s))
    # pure-end

def below__zero(ops : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(ops)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(ops)))
    Ensures(not (Result()) or (Forall(int, lambda i:
        not (((0) <= (i)) and ((i) <= (len(ops)))) or ((psum(0, i, ops)) >= (0)))))
    Ensures(not (not(Result())) or (Exists(int, lambda i:
        (((0) <= (i)) and ((i) <= (len(ops)))) and ((psum(0, i, ops)) < (0)))))
    # post-conditions-end

    # impl-start
    balance : int = 0
    i : int = 0
    
    while (i) < (len(ops)):
        # invariants-start
        Invariant(Acc(list_pred(ops)))
        Invariant(((0) <= (i)) and ((i) <= (len(ops))))
        Invariant((balance) == (psum(0, i, ops)))
        Invariant(Forall(int, lambda i: (not (((0) <= (i)) and ((i) < (len(ops)))) or ((psum(0, i + 1, ops)) == (psum(0, i, ops) + ops[i])), [[psum(0, i + 1, ops)]])))
        Invariant(Forall(int, lambda j:
            (not (((0) <= (j)) and ((j) <= (i))) or ((psum(0, j, ops)) >= (0)), [[psum(0, j, ops)]])))
        # invariants-end

        # assert-start
        Assert((psum(0, (i) + (1), ops)) == ((psum(0, i, ops)) + ((ops)[i])))
        # assert-end
        
        balance = (balance) + ((ops)[i])
        if (balance) < (0):
            return False
        i = (i) + (1)

    return True
    # impl-end
