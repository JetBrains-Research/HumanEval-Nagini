from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def encode(s : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or ((((97) <= ((s)[i])) and (((s)[i]) <= (122))) or (((65) <= ((s)[i])) and (((s)[i]) <= (90))))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures(Acc(list_pred(s)))
    Ensures((len(s)) == (len(Result())))
    Ensures(Forall(int, lambda i:
        not ((((0) <= (i)) and ((i) < (len(s)))) and (is__vowel((s)[i]))) or (((Result())[i]) == (rot2(swap__case((s)[i]))))))
    Ensures(Forall(int, lambda i:
        not ((((0) <= (i)) and ((i) < (len(s)))) and (not(is__vowel((s)[i])))) or (((Result())[i]) == (swap__case((s)[i])))))
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
            (not ((((0) <= (j)) and ((j) < (i))) and (is__vowel((s)[j]))) or (((t)[j]) == (rot2(swap__case((s)[j])))), [[rot2(swap__case((s)[j]))]])))
        Invariant(Forall(int, lambda j:
            (not ((((0) <= (j)) and ((j) < (i))) and (not(is__vowel((s)[j])))) or (((t)[j]) == (swap__case((s)[j]))), [[swap__case((s)[j])]])))
        # invariants-end
        if is__vowel((s)[i]):
            t = (t) + [rot2(swap__case((s)[i]))]
        else:
            t = (t) + [swap__case((s)[i])]
        i = (i) + (1)
    return t
    # impl-end

@Pure
def swap__case(c : int) -> int :
    # pure-start
    if ((97) <= (c)) and ((c) <= (122)):
        return (65) + ((c) - (97))
    elif True:
        return (97) + ((c) - (65))
    # pure-end

@Pure
def rot2(c : int) -> int :
    # pure-start
    return (c + 2)  
    # pure-end

@Pure
def is__vowel(c : int) -> bool :
    # pure-start
    return ((((((c) == (97)) or ((c) == (101))) or ((c) == (105))) or ((c) == (111))) or ((c) == (117))) or ((((((c) == (65)) or ((c) == (69))) or ((c) == (73))) or ((c) == (79))) or ((c) == (85)))
    # pure-end
