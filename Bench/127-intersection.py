from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def IsPrime(n : int) -> bool :
    # pure-start
    return ((n) > (1)) and (Forall(int, lambda k:
        not (((2) <= (k)) and ((k) < (n))) or (((n % k)) != (0))))
    # pure-end

#use-as-unpure
@Pure
def min(a : int, b : int) -> int :
    # pure-start
    if (a) <= (b):
        return a
    elif True:
        return b
    # pure-end

#use-as-unpure
@Pure
def max(a : int, b : int) -> int :
    # pure-start
    if (a) >= (b):
        return a
    elif True:
        return b
    # pure-end

def Intersection(start1 : int, end1 : int, start2 : int, end2 : int) -> str:
    # pre-conditions-start
    Requires(((start1) <= (end1)) and ((start2) <= (end2)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(((Result()) == ("YES")) or ((Result()) == ("NO")))
    Ensures(((Result()) == ("YES")) == (((max(start1, start2)) <= (min(end1, end2))) and (IsPrime(((min(end1, end2)) - (max(start1, start2))) + (1)))))
    # post-conditions-end

    # impl-start
    intersectionStart : int = max(start1, start2)
    intersectionEnd : int = min(end1, end2)
    if (intersectionStart) <= (intersectionEnd):
        length : int = ((intersectionEnd) - (intersectionStart)) + (1)
        if IsPrime(length):
            return "YES"
    return "NO"
    # impl-end
