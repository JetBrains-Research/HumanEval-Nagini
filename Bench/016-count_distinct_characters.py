from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def contains_char(s : List[int], c : int, i : int, j : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((97) <= ((s)[i])) and (((s)[i]) <= (122)))))
    Requires(0 <= i and i <= j and j <= len(s))
    Requires(((97) <= (c)) and ((c) <= (122)))
    # pre-conditions-end

    # pure-start
    if i == j:
        return False
    else:
        return s[j - 1] == c or contains_char(s, c, i, j - 1)
    # pure-end
    
@Pure 
def count_chars_inter(s : List[int], c : int) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((97) <= ((s)[i])) and (((s)[i]) <= (122)))))
    Requires(((97) <= (c)) and ((c) <= (123)))
    # pre-conditions-end

    # pure-start
    if c == 97:
        return 0
    else:
        return count_chars_inter(s, c - 1) + (1 if contains_char(s, c - 1, 0, len(s)) else 0)
    # pure-end

def count_distinct_characters(s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((97) <= ((s)[i])) and (((s)[i]) <= (122)))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(s)))) or (((97) <= ((s)[i])) and (((s)[i]) <= (122)))))
    Ensures((Result()) == count_chars_inter(s, 123))
    # post-conditions-end

    # impl-start
    c : int = int(0)
    i : int = int(97)
    while (i) <= (122):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((97) <= (i)) and ((i) <= (123)))
        Invariant(Forall(int, lambda i:
            not (((0) <= (i)) and ((i) < (len(s)))) or (((97) <= ((s)[i])) and (((s)[i]) <= (122)))))
        Invariant(c == count_chars_inter(s, i))
        # invariants-end
        if contains_char(s, i, 0, len(s)):
            c = c + 1
        i = i + 1
    return c
    # impl-end
