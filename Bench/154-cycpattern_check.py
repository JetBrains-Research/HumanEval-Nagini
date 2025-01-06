from typing import List
from nagini_contracts.contracts import *

@Pure
def IsSubstring(s : List[int], sub : List[int], n : int) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Acc(list_pred(sub)))
    # pure-pre-conditions-end

    # pure-start
    return ((len(s)) >= (len(sub))) and (Exists(int, lambda i:
        (((0) <= (i)) and ((i) < 1 + ((len(s)) - (len(sub))))) and (
            Forall(int, lambda y: (Implies(y >= 0 and y < len(sub), sub[(n + y) % len(sub)] == s[i + y]), [[sub[(n + y) % len(sub)] == s[i + y]]])))))
    # pure-end

def CycpatternCheck(word : List[int], pattern : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(word)))
    Requires(Acc(list_pred(pattern)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(word)))
    Ensures(Acc(list_pred(pattern)))
    Ensures(not (Result()) or (Exists(int, lambda i:
        (((0) <= (i)) and ((i) <= (len(pattern)))) and (IsSubstring(word, pattern, i)))))
    Ensures(not (not(Result())) or (Forall(int, lambda i:
        not (((0) <= (i)) and ((i) <= (len(pattern)))) or (not(IsSubstring(word, pattern, i))))))
    # post-conditions-end

    # impl-start
    i : int = 0
    while (i) <= (len(pattern)):
        # invariants-start
        Invariant(Acc(list_pred(word)))
        Invariant(Acc(list_pred(pattern)))
        Invariant(((0) <= (i)) and ((i) <= ((len(pattern)) + (1))))
        Invariant(Forall(int, lambda j:
            (Implies(((0) <= (j)) and ((j) < (i)), not(IsSubstring(word, pattern, j))), [[IsSubstring(word, pattern, j)]])))
        # invariants-end
        if IsSubstring(word, pattern, i):
            return True
        i = (i) + (1)
    return False
    # impl-end
