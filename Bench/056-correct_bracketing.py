from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def CalBal(s : List[int], i : int, j : int) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

    # impl-start
    if i == j:
        return 0
    else:
        return (1 if s[j - 1] == 0 else -1) + CalBal(s, i, j - 1)
    # impl-end

def correct_bracketing(s : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(s)))) or ((((s)[d_0_i_]) == (0)) or (((s)[d_0_i_]) == (1)))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(s)))) or ((((s)[d_0_i_]) == (0)) or (((s)[d_0_i_]) == (1)))))
    Ensures(Implies(Result(), Forall(int, lambda x: (Implies(x >= 0 and x <= len(s), CalBal(s, 0, x) >= 0)))))
    Ensures(Implies(Forall(int, lambda x: (Implies(x >= 0 and x <= len(s), CalBal(s, 0, x) >= 0))), Result()))
    # post-conditions-end

    # impl-start
    i : int = 0
    depth : int = 0
    result : int = True
    while i < len(s):
        # invariants-start
        Invariant(Acc(list_pred(s), 1/2))
        Invariant(0 <= i and i <= len(s))
        Invariant(Forall(int, lambda d_0_i_:
            not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(s)))) or ((((s)[d_0_i_]) == (0)) or (((s)[d_0_i_]) == (1)))))
        Invariant(Forall(int, lambda x : (Implies(x >= 0 and x < len(s), CalBal(s, 0, x + 1) == CalBal(s, 0, x) + (1 if s[x] == 0 else -1)), [[CalBal(s, 0, x + 1)]])))
        Invariant(depth >= 0)
        Invariant(depth == CalBal(s, 0, i)) 
        Invariant(CalBal(s, 0, i) >= 0)
        Invariant(Forall(int, lambda x: (Implies(x >= 0 and x <= i, CalBal(s, 0, x) >= 0), [[CalBal(s, 0, x) >= 0]])))
        # invariants-end
        # assert-start
        Assert(CalBal(s, 0, i + 1) == CalBal(s, 0, i) + (1 if s[i] == 0 else -1))
        # assert-end
        if s[i] == 0:
            depth = depth + 1
        else:
            depth = depth - 1
        if depth < 0:
            return False
        i = i + 1
    return result
    # impl-end