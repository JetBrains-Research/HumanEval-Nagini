from typing import List
from nagini_contracts.contracts import *

@Pure
def IsSubstring(s : List[int], sub : List[int], n : int) -> bool :
    Requires(Acc(list_pred(s)))
    Requires(Acc(list_pred(sub)))
    return ((len(s)) >= (len(sub))) and (Exists(int, lambda d_0_i_:
        (((0) <= (d_0_i_)) and ((d_0_i_) < 1 + ((len(s)) - (len(sub))))) and (
            Forall(int, lambda y: (Implies(y >= 0 and y < len(sub), sub[(n + y) % len(sub)] == s[d_0_i_ + y]), [[sub[(n + y) % len(sub)] == s[d_0_i_ + y]]])))))

def CycpatternCheck(word : List[int], pattern : List[int]) -> bool:
    Requires(Acc(list_pred(word)))
    Requires(Acc(list_pred(pattern)))
    Ensures(Acc(list_pred(word)))
    Ensures(Acc(list_pred(pattern)))
    Ensures(not (Result()) or (Exists(int, lambda d_1_i_:
        (((0) <= (d_1_i_)) and ((d_1_i_) <= (len(pattern)))) and (IsSubstring(word, pattern, d_1_i_)))))
    Ensures(not (not(Result())) or (Forall(int, lambda d_2_i_:
        not (((0) <= (d_2_i_)) and ((d_2_i_) <= (len(pattern)))) or (not(IsSubstring(word, pattern, d_2_i_))))))
    result = False # type : bool
    d_3_i_ = int(0) # type : int
    d_3_i_ = 0
    while (d_3_i_) <= (len(pattern)):
        Invariant(Acc(list_pred(word)))
        Invariant(Acc(list_pred(pattern)))
        Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= ((len(pattern)) + (1))))
        Invariant(Forall(int, lambda d_4_j_:
            (Implies(((0) <= (d_4_j_)) and ((d_4_j_) < (d_3_i_)), not(IsSubstring(word, pattern, d_4_j_))), [[IsSubstring(word, pattern, d_4_j_)]])))
        if IsSubstring(word, pattern, d_3_i_):
            result = True
            return result
        d_3_i_ = (d_3_i_) + (1)
    result = False
    return result