from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

#use-as-unpure
@Pure 
def encode__char(c : int) -> int :
    # pure-start
    return (c - 97 + 5) % 26 + 97
    # pure-end

#use-as-unpure
@Pure
def decode__char(c : int) -> int :
    # pure-start
    return ((c) - (97) - (5)) % 26 + 97
    # pure-end

def encode__shift(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((97) <= ((s)[i])) and (((s)[i]) <= (122)))))
    # pre-conditions-end
    # post-conditions-start 
    Ensures(Acc(list_pred(Result())))
    Ensures(Acc(list_pred(s)))
    Ensures((len(s)) == (len(Result())))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((Result())[i]) == (encode__char((s)[i])))))
    # post-conditions-end

    # impl-start
    t : List[int] = []
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(t)))
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant((len(t)) == (i))
        Invariant(Forall(int, lambda j:
            (not (((0) <= (j)) and ((j) < (i))) or (((t)[j]) == (encode__char((s)[j]))), [[encode__char((s)[j])]])))
        # invariants-end
        t = (t) + [encode__char((s)[i])]
        i = (i) + (1)
    return t
    # impl-end

def decode__shift(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((97) <= ((s)[i])) and (((s)[i]) <= (122)))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures(Acc(list_pred(s)))
    Ensures((len(s)) == (len(Result())))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((Result())[i]) == (decode__char((s)[i])))))
    # post-conditions-end

    # impl-start
    t : List[int] = []
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(t)))
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant((len(t)) == (i))
        Invariant(Forall(int, lambda j:
            (not (((0) <= (j)) and ((j) < (i))) or (((t)[j]) == (decode__char((s)[j]))), [[decode__char((s)[j])]])))
        # invariants-end
        t = (t) + [decode__char((s)[i])]
        i = (i) + (1)
    return t
    # impl-end
