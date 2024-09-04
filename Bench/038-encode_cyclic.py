from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def encode_cyclic(s: List[int]) -> List[int]:
    Requires(Acc(list_pred(s), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures(Acc(list_pred(s), 1/2))
    Ensures(len(s) == len(Result()))
    Ensures(Forall(int, lambda x: 
        (Implies(0 <= x and x < len(s) - len(s) % 3, Implies(x % 3 == 0, Result()[x] == s[x + 1])))))
    Ensures(Forall(int, lambda x: 
        (Implies(0 <= x and x < len(s) - len(s) % 3, Implies(x % 3 == 1, Result()[x] == s[x + 1])))))
    Ensures(Forall(int, lambda x: 
        (Implies(0 <= x and x < len(s) - len(s) % 3, Implies(x % 3 == 2, Result()[x] == s[x - 2])))))
    Ensures(Forall(int, lambda x:
        (Implies(len(s) - len(s) % 3 <= x and x < len(s), Result()[x] == s[x]))))
    
    res : List[int] = list(s)
    i = 0
    while i + 2 < len(s):
        Invariant(Acc(list_pred(res)))
        Invariant(Acc(list_pred(s),1/2))
        Invariant(0 <= i and i <= len(s))
        Invariant(len(s) == len(res))
        Invariant(i % 3 == 0)
        Invariant(Forall(int, lambda x: Implies(i <= x and x < len(s), res[x] == s[x])))
        Invariant(Forall(int, lambda x: 
            (Implies(0 <= x and x < i, Implies(x % 3 == 0, res[x] == s[x + 1])), [[res[x]]])))
        Invariant(Forall(int, lambda x: 
            (Implies(0 <= x and x < i, Implies(x % 3 == 1, res[x] == s[x + 1])), [[res[x]]])))
        Invariant(Forall(int, lambda x: 
            (Implies(0 <= x and x < i, Implies(x % 3 == 2, res[x] == s[x - 2])), [[res[x]]])))
        res[i] = s[i + 1]
        res[i + 1] = s[i + 2]
        res[i + 2] = s[i]
        i = i + 3
    Assert(i == len(s) - len(s) % 3)
    return res

def decode_cyclic(s: List[int]) -> List[int]:
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures(Acc(list_pred(s)))
    Ensures(len(s) == len(Result()))
    Ensures(Forall(int, lambda x:
        (Implies(len(s) - len(s) % 3 <= x and x < len(s), Result()[x] == s[x]))))
    Ensures(Forall(int, lambda x: 
        (Implies(0 <= x and x < len(s) - len(s) % 3, Implies(x % 3 == 0, Result()[x] == s[x + 2])))))
    Ensures(Forall(int, lambda x: 
        (Implies(0 <= x and x < len(s) - len(s) % 3, Implies(x % 3 == 1, Result()[x] == s[x - 1])))))
    return encode_cyclic(encode_cyclic(s))