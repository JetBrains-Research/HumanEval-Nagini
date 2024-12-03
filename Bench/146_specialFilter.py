from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def first__digit(n : int) -> int :
    # pre-conditions-start
    Requires(((0) <= (n)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(0 <= Result() and (Result()) < (10))
    # post-conditions-end

    # pure-start
    if n < 10:
        return n
    else:
        return first__digit(n // 10)
    # pure-end

@Pure
def last__digit(n : int) -> int :
    # pure-start
    return (n % 10)
    # pure-end

def specialFilter(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or (((Result())[i]) > (10))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or ((((first__digit((Result())[i]) % 2)) == (1)) and (((last__digit((Result())[i]) % 2)) == (1)))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or 
            (Exists(int, lambda x: x >= 0 and x < len(s) and s[x] == Result()[i]))))
    # post-conditions-end

    # impl-start
    r : List[int] = []
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(r)))
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant(Forall(int, lambda i:
            not (((0) <= (i)) and ((i) < (len(r)))) or (((r)[i]) > (10))))
        Invariant(Forall(int, lambda i:
            (not (((0) <= (i)) and ((i) < (len(r)))) or ((((first__digit((r)[i]) % 2)) == (1)) and (((last__digit((r)[i]) % 2)) == (1))), [[first__digit((r)[i])]])))
        Invariant(Forall(int, lambda i:
            not (((0) <= (i)) and ((i) < (len(r)))) or 
                (Exists(int, lambda x: x >= 0 and x < len(s) and s[x] == r[i]))))
        # invariants-end
        if ((((s)[i]) > (10)) and (((last__digit((s)[i]) % 2)) == (1))) and (((first__digit((s)[i]) % 2)) == (1)):
            r = (r) + [(s)[i]]
        i = (i) + (1)
    return r
    # impl-end
