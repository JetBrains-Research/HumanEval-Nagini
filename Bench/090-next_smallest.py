from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def next_smallest(s : List[int]) -> Optional[int]:
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(s)))
    Ensures((Result() is None) == (len(s) < 2))
    Ensures(Implies(Result() is not None, Exists(int, lambda x: x >= 0 and x < len(s) and s[x] == Result())))
    Ensures(Forall(int, lambda x: 
        Implies(x >= 0 and x < len(s), 
            Forall(int, lambda y: 
                Implies(y > x and y < len(s), 
                    s[x] <= Result() or s[y] <= Result())))))

    if len(s) < 2:
        return None
    
    res : Optional[int] = None
    mx : int = s[0]
    i = 1
    while i < len(s):
        Invariant(Acc(list_pred(s)))
        Invariant(len(s) >= 2)
        Invariant(0 <= i and i <= len(s))
        Invariant(Implies(i == 1, res is None))
        Invariant(Implies(res is not None, res <= mx))
        Invariant(Forall(int, lambda x: Implies(x >= 0 and x < i, s[x] <= mx)))
        Invariant(Implies(i > 1, res is not None))
        Invariant(Implies(i > 1, Forall(int, lambda x: 
            Implies(x >= 0 and x < i, s[x] == mx or s[x] <= res))))
        Invariant(Exists(int, lambda x: x >= 0 and x < i and s[x] == mx))
        Invariant(Implies(i > 1, Exists(int, lambda x: x >= 0 and x < i and s[x] == res)))
        Invariant(Forall(int, lambda x: 
            Implies(x >= 0 and x < i, 
                Forall(int, lambda y: 
                    Implies(y > x and y < i, 
                        s[x] <= res or s[y] <= res)))))

        if s[i] > mx:
            res = mx 
            mx = s[i]
        elif res is None or s[i] > res:
            res = s[i]
        i += 1
    return res
