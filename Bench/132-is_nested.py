from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def is_nested(s : List[int]) -> bool:
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(s)))
    Ensures(Implies(Result(), Exists(int, lambda x: 
            x >= 0 and x < len(s) and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < len(s) and s[y] == 0 and 
                        Exists(int, lambda z: 
                            z > y and z < len(s) and s[z] == 1 and 
                                Exists(int, lambda w: 
                                    w > z and w < len(s) and s[w] == 1))))))
    Ensures(Implies(Exists(int, lambda x: 
            x >= 0 and x < len(s) and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < len(s) and s[y] == 0 and 
                        Exists(int, lambda z: 
                            z > y and z < len(s) and s[z] == 1 and 
                                Exists(int, lambda w: 
                                    w > z and w < len(s) and s[w] == 1)))), Result()))

    bal = 0
    i = 0
    while i < len(s) and bal < 2:
        Invariant(Acc(list_pred(s)))
        Invariant(0 <= i and i <= len(s))
        Invariant(0 <= bal and bal <= 2)
        Invariant(Implies(bal == 1, Exists(int, lambda x: x >= 0 and x < i and s[x] == 0)))
        Invariant(Implies(Exists(int, lambda x: x >= 0 and x < i and s[x] == 0), bal >= 1))
        Invariant(Implies(bal == 2, Exists(int, lambda x: 
            x >= 0 and x < i and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < i and s[y] == 0))))
        Invariant(Implies(Exists(int, lambda x: 
            x >= 0 and x < i and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < i and s[y] == 0)), bal == 2))
        Invariant(not(Exists(int, lambda x: 
            x >= 0 and x < i and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < i and s[y] == 0 and 
                        Exists(int, lambda z: 
                            z > y and z < i and s[z] == 1)))))
        if s[i] == 0:
            bal = bal + 1
        i = i + 1
    
    if bal < 2:
        Assert(not(Exists(int, lambda x: 
            x >= 0 and x < i and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < i and s[y] == 0))))
        return False 
    
    
    while i < len(s) and bal > 0:
        Invariant(Acc(list_pred(s)))
        Invariant(0 <= i and i <= len(s))
        Invariant(0 <= bal and bal <= 2)
        Invariant(Exists(int, lambda x: 
            x >= 0 and x < i and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < i and s[y] == 0)))
        Invariant(Implies(bal <= 1, Exists(int, lambda x: 
            x >= 0 and x < i and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < i and s[y] == 0 and 
                        Exists(int, lambda z: 
                            z > y and z < i and s[z] == 1)))))
        Invariant(Implies(bal == 0, Exists(int, lambda x: 
            x >= 0 and x < i and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < i and s[y] == 0 and 
                        Exists(int, lambda z: 
                            z > y and z < i and s[z] == 1 and 
                                Exists(int, lambda w: 
                                    w > z and w < i and s[w] == 1))))))
        Invariant(Implies(Exists(int, lambda x: 
            x >= 0 and x < i and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < i and s[y] == 0 and 
                        Exists(int, lambda z: 
                            z > y and z < i and s[z] == 1))), bal <= 1))
        Invariant(Implies(Exists(int, lambda x: 
            x >= 0 and x < i and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < i and s[y] == 0 and 
                        Exists(int, lambda z: 
                            z > y and z < i and s[z] == 1 and 
                                Exists(int, lambda w: 
                                    w > z and w < i and s[w] == 1)))), bal == 0))
        if s[i] == 1:
            bal = bal - 1
            Assert(Exists(int, lambda x: 
                x >= 0 and x < i and s[x] == 0 and 
                    Exists(int, lambda y: 
                        y > x and y < i and s[y] == 0 and 
                            Exists(int, lambda z: 
                                z > y and z <= i and s[z] == 1))))
            Assert(bal <= 1)
        i = i + 1
    
    if bal > 0: 
        Assert(not(Exists(int, lambda x: 
            x >= 0 and x < i and s[x] == 0 and 
                Exists(int, lambda y: 
                    y > x and y < i and s[y] == 0 and 
                        Exists(int, lambda z: 
                            z > y and z < i and s[z] == 1 and 
                                Exists(int, lambda w: 
                                    w > z and w < i and s[w] == 1))))))
        return False
    
    return True

