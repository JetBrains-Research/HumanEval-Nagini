from typing import List
from nagini_contracts.contracts import *

@Pure
def IsVowel(c : int) -> bool :
    return ((((((((((c) == (97)) or ((c) == (101))) or ((c) == (105))) or ((c) == (111))) or ((c) == (117))) or ((c) == (65))) or ((c) == (69))) or ((c) == (73))) or ((c) == (79))) or ((c) == (85))

@Pure
def IsConsonant(c : int) -> bool :
    return ((((65) <= (c)) and ((c) <= (90))) or (((97) <= (c)) and ((c) <= (122)))) and (not(IsVowel(c)))

def get__closest__vowel(word : List[int]) -> List[int]:
    Requires(Acc(list_pred(word)))
    Requires(Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(word)))) or ((((65) <= ((word)[d_0_i_])) and (((word)[d_0_i_]) <= (90))) or (((97) <= ((word)[d_0_i_])) and (((word)[d_0_i_]) <= (122))))))
    Ensures(Acc(list_pred(word)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) <= (1))
    Ensures(not ((len(Result())) == (1)) or (IsVowel((Result())[0])))
    Ensures(not ((len(Result())) == (1)) or (Exists(int, lambda d_1_i_:
        ((((((1) <= (d_1_i_)) and (((d_1_i_) + (1)) < (len(word)))) and (IsVowel((word)[d_1_i_]))) and (IsConsonant((word)[(d_1_i_) - (1)]))) and (IsConsonant((word)[(d_1_i_) + (1)]))) and (
            Forall(int, lambda j:
                not (j > d_1_i_ and j <= len(word) - 2) or (((not(IsVowel((word)[j]))) or (not(IsConsonant((word)[j - 1])))) or (not(IsConsonant((word)[j + 1])))))))))
    result = list([int(0)] * 0) # type : List[int]
    if (len(word)) < (3):
        result = []
        return result
    d_5_i_ = int(0) # type : int
    d_5_i_ = (len(word)) - (2)
    while (d_5_i_) > (0):
        Invariant(Acc(list_pred(word)))
        Invariant(Acc(list_pred(result)))
        Invariant(((0) <= (d_5_i_)) and ((d_5_i_) <= ((len(word)) - (2))))
        Invariant(Forall(int, lambda d_6_j_:
            not (((d_5_i_) < (d_6_j_)) and ((d_6_j_) < ((len(word)) - (1)))) or (((not(IsVowel((word)[d_6_j_]))) or (not(IsConsonant((word)[(d_6_j_) - (1)])))) or (not(IsConsonant((word)[(d_6_j_) + (1)]))))))
        Invariant(Forall(int, lambda j:
                not (j > d_5_i_ and j <= len(word) - 2) or (((not(IsVowel((word)[j]))) or (not(IsConsonant((word)[j - 1])))) or (not(IsConsonant((word)[j + 1]))))))
        if ((IsVowel((word)[d_5_i_])) and (IsConsonant((word)[(d_5_i_) - (1)]))) and (IsConsonant((word)[(d_5_i_) + (1)])):
            result = [(word)[d_5_i_]]
            return result
        d_5_i_ = (d_5_i_) - (1)
    result = []
    return result
