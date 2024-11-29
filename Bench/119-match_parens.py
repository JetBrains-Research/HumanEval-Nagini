from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def CalBal(s : List[int], i : int, j : int, acc : int) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

    # pure-start
    if i == j:
        return acc
    else:
        return (1 if s[j - 1] == 0 else -1) + CalBal(s, i, j - 1, acc)
    # pure-end
    
def checkFixed(s1 : List[int], s2 : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s1)))
    Requires(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(s1)))) or ((((s1)[d_0_i_]) == (0)) or (((s1)[d_0_i_]) == (1)))))
    Requires(Acc(list_pred(s2)))
    Requires(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(s2)))) or ((((s2)[d_0_i_]) == (0)) or (((s2)[d_0_i_]) == (1)))))
    # pre-conditions-end

    # post-conditions-start
    Ensures(Acc(list_pred(s1)))
    Ensures(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(s1)))) or ((((s1)[d_0_i_]) == (0)) or (((s1)[d_0_i_]) == (1)))))
    Ensures(Acc(list_pred(s2)))
    Ensures(Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(s2)))) or ((((s2)[d_0_i_]) == (0)) or (((s2)[d_0_i_]) == (1)))))
    
    Ensures(Implies(Result(), Forall(int, lambda x: (Implies(x >= 0 and x <= len(s1), CalBal(s1, 0, x, 0) >= 0)))))
    Ensures(Implies(Result(), Forall(int, lambda x: (Implies(x >= 0 and x <= len(s2), CalBal(s1, 0, len(s1), 0) + CalBal(s2, 0, x, 0) >= 0)))))
    Ensures(Implies(not(Result()), 
        Exists(int, lambda x: x >= 0 and x <= len(s1) and CalBal(s1, 0, x, 0) < 0) or 
        Exists(int, lambda x: x >= 0 and x <= len(s2) and CalBal(s1, 0, len(s1), 0) + CalBal(s2, 0, x, 0) < 0)))
    # post-conditions-end

    # impl-start
    bal : int = 0
    i : int = 0

    while i < len(s1):
        # invariants-start
        Invariant(Acc(list_pred(s1), 1/2))
        Invariant(0 <= i and i <= len(s1))
        Invariant(Forall(int, lambda d_0_i_:
            not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(s1)))) or ((((s1)[d_0_i_]) == (0)) or (((s1)[d_0_i_]) == (1)))))
        Invariant(Forall(int, lambda x : (Implies(x >= 0 and x < len(s1), CalBal(s1, 0, x + 1, 0) == CalBal(s1, 0, x, 0) + (1 if s1[x] == 0 else -1)), [[CalBal(s1, 0, x + 1, 0)]])))
        Invariant(bal == CalBal(s1, 0, i, 0))
        Invariant(bal >= 0)
        Invariant(Forall(int, lambda x: (Implies(x >= 0 and x <= i, CalBal(s1, 0, x, 0) >= 0), [[CalBal(s1, 0, x, 0) >= 0]])))
        # invariants-end
        
        # assert-start
        Assert(CalBal(s1, 0, i + 1, 0) == CalBal(s1, 0, i, 0) + (1 if s1[i] == 0 else -1))
        # assert-end
        if s1[i] == 0:
            bal = bal + 1
        else:
            bal = bal - 1

        if bal < 0:
            # assert-start
            Assert(Exists(int, lambda x: x >= 0 and x <= len(s1) and CalBal(s1, 0, x, 0) < 0))
            # assert-end
            return False
        i = i + 1

    i = 0 
    while i < len(s2):
        # invariants-start
        Invariant(Acc(list_pred(s1), 1/2))
        Invariant(Acc(list_pred(s2), 1/2))
        Invariant(0 <= i and i <= len(s2))
        Invariant(Forall(int, lambda d_0_i_:
            not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(s2)))) or ((((s2)[d_0_i_]) == (0)) or (((s2)[d_0_i_]) == (1)))))
        Invariant(Forall(int, lambda x: (Implies(x >= 0 and x < len(s1), CalBal(s1, 0, x, 0) >= 0), [[CalBal(s1, 0, x, 0) >= 0]])))
        Invariant(Forall(int, lambda x : (Implies(x >= 0 and x < len(s2), CalBal(s2, 0, x + 1, 0) == CalBal(s2, 0, x, 0) + (1 if s2[x] == 0 else -1)), [[CalBal(s2, 0, x + 1, 0)]])))
        Invariant(bal == CalBal(s1, 0, len(s1), 0) + CalBal(s2, 0, i, 0))
        Invariant(bal >= 0)
        Invariant(Forall(int, lambda x: (Implies(x >= 0 and x <= len(s1), CalBal(s1, 0, x, 0) >= 0), [[CalBal(s1, 0, x, 0) >= 0]])))
        Invariant(Forall(int, lambda x: (Implies(x >= 0 and x <= i, CalBal(s1, 0, len(s1), 0) + CalBal(s2, 0, x, 0) >= 0), [[CalBal(s1, 0, len(s1), 0) + CalBal(s2, 0, x, 0) >= 0]])))
        # invariants-end
        
        if s2[i] == 0:
            bal = bal + 1
        else:
            bal = bal - 1

        if bal < 0:
            # assert-start
            Assert(CalBal(s1, 0, len(s1), 0) + CalBal(s2, 0, i + 1, 0) < 0)
            Assert(Exists(int, lambda x: x >= 0 and x <= len(s2) and CalBal(s1, 0, len(s1), 0) + CalBal(s2, 0, x, 0) < 0))
            # assert-end
            return False
        i = i + 1

    return True
    # impl-end
