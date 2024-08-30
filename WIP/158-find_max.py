from typing import List
from nagini_contracts.contracts import *

@Pure 
def withinRange(x : int) -> bool:
    return 97 <= x and x <= 122

@Pure
def withinRangeString(s : List[int]) -> bool:
    Requires(Acc(list_pred(s), 1/2))
    return Forall(int, lambda x: Implies(x >= 0 and x < len(s), withinRange(s[x])))

@Pure 
def EqArrays(a : List[int], x : List[int]) -> bool :
    Requires(Acc(list_pred(a), 1/2))
    Requires(Acc(list_pred(x), 1/2))
    return len(a) == len(x) and Forall(int, lambda d_0_i_: 
        (Implies(0 <= d_0_i_ and d_0_i_ < len(a), (a)[d_0_i_] == x[d_0_i_]), [[a[d_0_i_] == x[d_0_i_]]]))

@Pure
def contains_char(s : List[int], c : int, i : int, j : int) -> bool:
    Requires(Acc(list_pred(s), 1/2))
    Requires(withinRangeString(s))
    Requires(0 <= i and i <= j and j <= len(s))
    Requires(withinRange(c))
    if i == j:
        return False
    else:
        return s[j - 1] == c or contains_char(s, c, i, j - 1)
    
@Pure 
def count_chars_inter(s : List[int], c : int) -> int:
    Requires(Acc(list_pred(s), 1/2))
    Requires(withinRangeString(s))
    Requires(((97) <= (c)) and ((c) <= (123)))
    if c == 97:
        return 0
    else:
        return count_chars_inter(s, c - 1) + (1 if contains_char(s, c - 1, 0, len(s)) else 0)
    
@Pure 
def compare_strings(s1 : List[int], s2 : List[int]) -> bool:
    Requires(Acc(list_pred(s1), 1/2))
    Requires(Acc(list_pred(s2), 1/2))
    Requires(withinRangeString(s2))
    Requires(withinRangeString(s1))
    return count_chars_inter(s1, 123) <= count_chars_inter(s2, 123)

@Pure 
def contains_char_compare(s1 : List[int], s2 : List[int], x : int) -> bool:
    Requires(Acc(list_pred(s1), 1/2))
    Requires(Acc(list_pred(s2), 1/2))
    Requires(withinRangeString(s1))
    Requires(withinRangeString(s2))
    Requires(withinRange(x))
    Requires(len(s1) == len(s2))
    Requires(Forall(int, lambda x: Implies(0 <= x and x < len(s1), s1[x] == s2[x])))
    return contains_char(s1, x, 0, len(s1)) == contains_char(s2, x, 0, len(s2))

def find__max(strings : List[List[int]]) -> List[int]:
    Requires(Acc(list_pred(strings), 1/2))
    Requires(Forall(strings, lambda x : Acc(list_pred(x), 1/2)))
    Requires((len(strings)) > (0))
    # Requires(Forall(int, lambda y:
    #     Implies(y >= 0 and y < len(strings), Forall(int, lambda x: 
    #         Implies(x >= 0 and x < len(strings[y]), strings[y][x] >= 97 and strings[y][x] <= 122)))))
    Requires(Forall(strings, lambda y: withinRangeString(y)))
    Ensures(Acc(list_pred(strings), 1/2))
    Ensures(Forall(strings, lambda x : Acc(list_pred(x), 1/2)))
    Ensures(Forall(strings, lambda y: withinRangeString(y)))
    # Ensures(Forall(int, lambda y:
    #     Implies(y >= 0 and y < len(strings), Forall(int, lambda x: 
    #         Implies(x >= 0 and x < len(strings[y]), strings[y][x] >= 97 and strings[y][x] <= 122)))))
    Ensures(Acc(list_pred(Result()), 1/2))
    # Ensures(Exists(strings, lambda x: EqArrays(x, Result())))
    Ensures(withinRangeString(Result()))
    # Ensures(Forall(int, lambda x:
    #     Implies(x >= 0 and x < len(strings), count_chars_inter(Result(), 123) >= count_chars_inter(strings[x], 123))))
    s : List[int] = list((strings)[0])
    d_3_i_ = int(0) # type : int
    d_3_i_ = 1
    # Assert(EqArrays(strings[0], s))
    # Assert(Exists(int, lambda x: x >= 0 and x < d_3_i_ and (len(strings[x]) == len(s))))
    # Assert(Exists(strings, lambda x: EqArrays(x, s)))
    Assert(withinRangeString(s))
    Assert(Forall(int, lambda x: Implies(x >= 0 and x < len(s), s[x] == strings[0][x])) and len(s) == len(strings[0]))
    Assert(contains_char_compare(s, s, 100))
    # Assert(Forall(int, lambda x: (Implies(withinRange(x), contains_char_compare(strings[0], s, x)), [[contains_char_compare(strings[0], s, x)]])))
    # Assert(Forall(int, lambda x: (Implies(withinRange(x), contains_char_compare(strings[0], s, x)), [[contains_char_compare(strings[0], s, x)]])))
    # Assert(count_chars_inter(strings[0], 123) == count_chars_inter(s, 123))
    # Assert(compare_strings(strings[0], s))
    # while (d_3_i_) < (len(strings)):
    #     Invariant(Acc(list_pred(strings), 1/2))
    #     Invariant(Forall(strings, lambda x : Acc(list_pred(x), 1/2)))
    #     Invariant(Forall(strings, lambda y: withinRangeString(y)))
    #     Invariant(Forall(int, lambda y:
    #         (Implies(y >= 0 and y < len(strings), withinRangeString(strings[y])), 
    #             [[]])))
    #     Invariant(((1) <= (d_3_i_)) and ((d_3_i_) <= (len(strings))))
    #     Invariant(Acc(list_pred(s), 1/2))
    #     Invariant(withinRangeString(s))
    #     # Invariant(Exists(strings, lambda x: EqArrays(x, s)))
    #     # Invariant(Forall(int, lambda x: 
    #     #     (Implies(x >= 0 and x < d_3_i_, compare_strings(strings[x], s)), [[compare_strings(strings[x], s)]])))
    #     if (count_chars_inter((strings)[d_3_i_], 123)) > (count_chars_inter(s, 123)):
    #         s = list((strings)[d_3_i_])
    #         # Assert(Forall(int, lambda x: 
    #         #     (Implies(x >= 0 and x <= d_3_i_, compare_strings(strings[x], s)), [[compare_strings(strings[x], s)]])))
    #     # Assert(Forall(int, lambda x: 
    #     #     (Implies(x >= 0 and x <= d_3_i_, compare_strings(strings[x], s)), [[compare_strings(strings[x], s)]])))
    #     d_3_i_ = (d_3_i_) + (1)
    return s
