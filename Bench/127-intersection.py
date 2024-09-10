from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def IsPrime(n : int) -> bool :
    # impl-start
    return ((n) > (1)) and (Forall(int, lambda d_0_k_:
        not (((2) <= (d_0_k_)) and ((d_0_k_) < (n))) or (((n % d_0_k_)) != (0))))
    # impl-end

@Pure
def min(a : int, b : int) -> int :
    # impl-start
    if (a) <= (b):
        return a
    elif True:
        return b
    # impl-end

@Pure
def max(a : int, b : int) -> int :
    # impl-start
    if (a) >= (b):
        return a
    elif True:
        return b
    # impl-end

def Intersection(start1 : int, end1 : int, start2 : int, end2 : int) -> str:
    # pre-conditions-start
    Requires(((start1) <= (end1)) and ((start2) <= (end2)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(((Result()) == ("YES")) or ((Result()) == ("NO")))
    Ensures(((Result()) == ("YES")) == (((max(start1, start2)) <= (min(end1, end2))) and (IsPrime(((min(end1, end2)) - (max(start1, start2))) + (1)))))
    # post-conditions-end

    # impl-start
    result = "" # type : str
    d_1_intersectionStart_ = int(0) # type : int
    d_1_intersectionStart_ = max(start1, start2)
    d_2_intersectionEnd_ = int(0) # type : int
    d_2_intersectionEnd_ = min(end1, end2)
    if (d_1_intersectionStart_) <= (d_2_intersectionEnd_):
        d_3_length_ = int(0) # type : int
        d_3_length_ = ((d_2_intersectionEnd_) - (d_1_intersectionStart_)) + (1)
        if IsPrime(d_3_length_):
            result = "YES"
            return result
    result = "NO"
    return result
    # impl-end
