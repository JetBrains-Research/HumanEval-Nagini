from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def parseparengroup(s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(contains12(s))
    Requires(get_len(s))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s), 1/2))
    Ensures(contains12(s))
    Ensures(get_len(s))
    Ensures((Result()) >= (0))
    # post-conditions-end

    # impl-start
    depth : int = 0
    max__depth : int = 0
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s), 1/2))
        Invariant(((i) >= (0)) and ((i) <= (len(s))))
        Invariant(max__depth >= 0)
        Invariant(contains12(s))
        Invariant(get_len(s))
        # invariants-end
        c : int = (s)[i]
        if (c) == (1):
            depth = (depth) + (1)
            if (depth) > (max__depth):
                max__depth = depth
        else:
            depth = (depth) - (1)
        i = (i) + (1)
    return max__depth
    # impl-end

@Pure 
def get_len(s : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    # pre-conditions-end

    # pure-start
    return len(s) > 0
    # pure-end

@Pure 
def contains12(s : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    # pre-conditions-end

    # pure-start
    return Forall(int, lambda i: 
        Implies(i >= 0 and i < len(s), s[i] == 1 or s[i] == 2))
    # pure-end

def split(s : List[int]) -> List[List[int]]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(s)))) or (((((s)[i]) == (1)) or (((s)[i]) == (2))) or (((s)[i]) == (3)))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(ResultT(List[List[int]]))))
    Ensures(Forall(ResultT(List[List[int]]), lambda x: Acc(list_pred(x), 1/2)))
    Ensures(Forall(int, lambda j:
        Implies(j >= 0 and j < len(ResultT(List[List[int]])), (get_len(ResultT(List[List[int]])[j])))))
    Ensures(Forall(int, lambda j:
        (Implies(j >= 0 and j < len(Result()), 
            contains12(Result()[j])), [[contains12(Result()[j])]])))
    # post-conditions-end

    # impl-start
    res : List[List[int]] = []
    current__string : List[int] = []
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(res)))
        Invariant(Forall(res, lambda x: Acc(list_pred(x), 1/2)))
        Invariant(Acc(list_pred(current__string)))
        Invariant(Acc(list_pred(s)))
        Invariant(((i) >= (0)) and ((i) <= (len(s))))
        Invariant(Forall(int, lambda i:
            (not (((i) >= (0)) and ((i) < (len(s)))) or (((((s)[i]) == (1)) or 
             (((s)[i]) == (2))) or (((s)[i]) == (3))), [[]])))
        Invariant(Forall(int, lambda i:
            (not (((i) >= (0)) and ((i) < (len(current__string)))) or 
             (((((current__string)[i]) == (1)) or (((current__string)[i]) == (2)))), [[]])))
        Invariant(Forall(int, lambda j:
            (Implies(j >= 0 and j < len(res), ((get_len(res[j])))), [[]])))
        Invariant(Forall(int, lambda j:
            (Implies(j >= 0 and j < len(res), 
                contains12(res[j])), [[contains12(res[j])]])))
        # invariants-end
        if ((s)[i]) == (3):
            if len(current__string) > 0:
                d_7_copy = list(current__string)
                res = (res) + [d_7_copy]
                current__string = []
        else:
            current__string = (current__string) + [(s)[i]]
        i = (i) + (1)
    if len(current__string) > 0:
        d_7_copy = list(current__string)
        # assert-start
        Assert(get_len(d_7_copy))
        # assert-end
        res = (res) + [d_7_copy]
        current__string =  []
    return res
    # impl-end

def parse__nested__parens(paren__string : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(paren__string)))
    Requires(Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(paren__string)))) or (((((paren__string)[i]) == (3)) or (((paren__string)[i]) == (1))) or (((paren__string)[i]) == (2)))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(ResultT(List[int]), lambda x: ((x) >= (0))))
    # post-conditions-end

    # impl-start
    res : List[int] = []
    strings : List[List[int]] = split(paren__string)
    i : int = int(0)
    while (i) < (len(strings)):
        # invariants-start
        Invariant(Acc(list_pred(strings)))
        Invariant(Acc(list_pred(res)))
        Invariant(Forall(strings, lambda x: Acc(list_pred(x), 1/2)))
        Invariant(0 <= i and i <= len(strings))
        Invariant(Forall(res, lambda x: ((x) >= (0))))
        Invariant(Forall(int, lambda j:
            Implies(j >= 0 and j < len(strings), (get_len(strings[j])))))
        Invariant(Forall(int, lambda j:
            (Implies(j >= 0 and j < len(strings), 
                contains12(strings[j])), [[contains12(strings[j])]])))
        # invariants-end
        cur : int = parseparengroup((strings)[i])
        res = (res) + [cur]
        i = (i) + (1)
    return res
    # impl-end
