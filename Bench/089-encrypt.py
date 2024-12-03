from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def rot__sym(c : int) -> int :
    # pre-conditions-start
    Requires(c >= 0 and c <= 25)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() >= 0 and Result() <= 25)
    # post-conditions-end

    # pure-start
    alph : int = c - 0
    return ((alph) + ((2) * (2))) % 26
    # pure-end

def encrypt(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((0) <= ((s)[i])) and (((s)[i]) <= (25)))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (len(s)))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((0) <= ((s)[i])) and (((s)[i]) <= (25)))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or (((0) <= ((Result())[i])) and (((Result())[i]) <= (25)))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((Result())[i]) == (rot__sym((s)[i])))))
    # post-conditions-end

    # impl-start
    r : List[int] = []
    i : int = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(Acc(list_pred(r)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant((len(r)) == (i))
        Invariant(Forall(int, lambda i:
            not (((0) <= (i)) and ((i) < (len(s)))) or (((0) <= ((s)[i])) and (((s)[i]) <= (25)))))    
        Invariant(Forall(int, lambda i:
            not (((0) <= (i)) and ((i) < (len(r)))) or (((0) <= ((r)[i])) and (((r)[i]) <= (25)))))  
        Invariant(Forall(int, lambda j:
            (not (((0) <= (j)) and ((j) < (i))) or (((r)[j]) == (rot__sym((s)[j]))), [[rot__sym((s)[j])]])))
        # invariants-end
        r = (r) + [rot__sym((s)[i])]
        i = (i) + (1)
    return r
    # impl-end
