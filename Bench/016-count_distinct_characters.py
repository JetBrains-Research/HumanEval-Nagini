from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def contains_char(s : List[int], c : int, i : int, j : int) -> bool:
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(s)))) or (((97) <= ((s)[d_0_i_])) and (((s)[d_0_i_]) <= (122)))))
    Requires(0 <= i and i <= j and j <= len(s))
    Requires(((97) <= (c)) and ((c) <= (122)))
    if i == j:
        return False
    else:
        return s[j - 1] == c or contains_char(s, c, i, j - 1)
    
@Pure 
def count_chars_inter(s : List[int], c : int) -> int:
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(s)))) or (((97) <= ((s)[d_0_i_])) and (((s)[d_0_i_]) <= (122)))))
    Requires(((97) <= (c)) and ((c) <= (123)))
    if c == 97:
        return 0
    else:
        return count_chars_inter(s, c - 1) + (1 if contains_char(s, c - 1, 0, len(s)) else 0)

def count_distinct_characters(s : List[int]) -> int:
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) or (((97) <= ((s)[d_1_i_])) and (((s)[d_1_i_]) <= (122)))))
    Ensures(Acc(list_pred(s)))
    Ensures(Forall(int, lambda d_1_i_:
        not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) or (((97) <= ((s)[d_1_i_])) and (((s)[d_1_i_]) <= (122)))))
    Ensures((Result()) == count_chars_inter(s, 123))
    c = int(0) # type : int
    d_2_i_ = int(97) # type : int
    while (d_2_i_) <= (122):
        Invariant(Acc(list_pred(s)))
        Invariant(((97) <= (d_2_i_)) and ((d_2_i_) <= (123)))
        Invariant(Forall(int, lambda d_1_i_:
            not (((0) <= (d_1_i_)) and ((d_1_i_) < (len(s)))) or (((97) <= ((s)[d_1_i_])) and (((s)[d_1_i_]) <= (122)))))
        Invariant(c == count_chars_inter(s, d_2_i_))
        if contains_char(s, d_2_i_, 0, len(s)):
            c = c + 1
        d_2_i_ = d_2_i_ + 1
    return c