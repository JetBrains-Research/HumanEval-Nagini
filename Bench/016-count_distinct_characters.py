from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def contains_char(s : List[int], c : int, i : int, j : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(s)))) or (((97) <= ((s)[d_0_i_])) and (((s)[d_0_i_]) <= (122)))))
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
    Requires(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(s)))) or (((97) <= ((s)[d_0_i_])) and (((s)[d_0_i_]) <= (122)))))
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
    Requires(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) or (((97) <= ((s)[d_1_i_])) and (((s)[d_1_i_]) <= (122)))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) or (((97) <= ((s)[d_1_i_])) and (((s)[d_1_i_]) <= (122)))))
    Ensures((Result()) == count_chars_inter(s, 123))
    # post-conditions-end

    # impl-start
    c : int = int(0)
    d_2_i_ : int = int(97)
    while (d_2_i_) <= (122):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((97) <= (d_2_i_)) and ((d_2_i_) <= (123)))
        Invariant(Forall(int, lambda d_1_i_:
            not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) or (((97) <= ((s)[d_1_i_])) and (((s)[d_1_i_]) <= (122)))))
        Invariant(c == count_chars_inter(s, d_2_i_))
        # invariants-end
        if contains_char(s, d_2_i_, 0, len(s)):
            c = c + 1
        d_2_i_ = d_2_i_ + 1
    return c
    # impl-end
