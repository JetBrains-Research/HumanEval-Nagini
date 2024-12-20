from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def checkSubstring(s : List[int], sub : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(Acc(list_pred(sub), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s), 1/2))
    Ensures(Acc(list_pred(sub), 1/2))
    # post-conditions-end

    # impl-start
    result : bool = False
    if (len(sub)) == (0):
        result = True
    elif (len(s)) >= (len(sub)):
        i : int = 0
        while (i) <= ((len(s)) - (len(sub))):
            # invariants-start
            Invariant(Acc(list_pred(s), 1/2))
            Invariant(Acc(list_pred(sub), 1/2))
            Invariant(len(s) - len(sub) >= 0)
            Invariant(((0) <= (i)) and ((i) <= 1 + ((len(s)) - (len(sub)))))
            # invariants-end
            x = 0 
            fl = True
            while x < len(sub):
                # invariants-start
                Invariant(Acc(list_pred(s), 1/2))
                Invariant(Acc(list_pred(sub), 1/2))
                Invariant(len(s) - len(sub) >= 0)
                Invariant(((0) <= (i)) and ((i) <= ((len(s)) - (len(sub)))))
                Invariant(x >= 0 and x <= len(sub))
                # invariants-end
                if sub[x] != s[i + x]:
                    fl = False
                    break
                x = x + 1
            if fl:
                result = True
            i = (i) + (1)
    return result
    # impl-end

@Pure 
def EqArrays(a : List[int], x : List[int]) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(a)))
    Requires(Acc(list_pred(x)))
    # pure-pre-conditions-end

    # pure-start
    return len(a) == len(x) and Forall(int, lambda i: Implies(0 <= i and i < len(a), (a)[i] == x[i]))
    # pure-end

@Pure 
def InArray(a : List[List[int]], x : List[int]) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(a)))
    Requires(Acc(list_pred(x)))
    Requires(Forall(a, lambda s: Acc(list_pred(s))))
    # pure-pre-conditions-end

    # pure-start
    return Exists(int, lambda s:
        (Implies(((0) <= (s)) and ((s) < (len((a)))), 
            EqArrays(a[s], x))))
    # pure-end


def filter__by__substring(strings : List[List[int]], substring : List[int]) -> List[List[int]]:
    # pre-conditions-start
    Requires(Acc(list_pred(strings)))
    Requires(Forall(strings, lambda s: Acc(list_pred(s))))
    Requires(Acc(list_pred(substring)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(strings)))
    Ensures(Forall(strings, lambda s: Acc(list_pred(s))))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(ResultT(List[List[int]]), lambda s: Acc(list_pred(s))))
    Ensures((len(Result())) <= (len(strings)))
    Ensures(Forall(int, lambda i:
        (Implies(0 <= i and i < len(Result()), InArray(strings, Result()[i])))))
    # post-conditions-end

    # impl-start
    res : List[List[int]] = []
    i : int = 0
    while (i) < (len(strings)):
        # invariants-start
        Invariant(Acc(list_pred(res)))
        Invariant(Acc(list_pred(strings)))
        Invariant(Acc(list_pred(substring)))
        Invariant(Forall(strings, lambda s: Acc(list_pred(s))))
        Invariant(Forall(res, lambda s: Acc(list_pred(s))))
        Invariant(((0) <= (i)) and ((i) <= (len(strings))))
        Invariant((len(res)) <= (i))
        Invariant(Forall(int, lambda i:
            (Implies(0 <= i and i < len(res), InArray(strings, res[i])), [[InArray(strings, res[i])]])))
        # invariants-end
        check : bool = checkSubstring((strings)[i], substring)
        if check:
            cpy = list((strings)[i])
            res = (res) + [cpy]
        i = (i) + (1)
    return res
    # impl-end
