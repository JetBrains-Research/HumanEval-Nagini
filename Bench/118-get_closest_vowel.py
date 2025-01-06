from typing import List
from nagini_contracts.contracts import *

@Pure
def IsVowel(c : int) -> bool :
    # pure-start
    return ((((((((((c) == (97)) or ((c) == (101))) or ((c) == (105))) or ((c) == (111))) or ((c) == (117))) or ((c) == (65))) or ((c) == (69))) or ((c) == (73))) or ((c) == (79))) or ((c) == (85))
    # pure-end

@Pure
def IsConsonant(c : int) -> bool :
    # pure-start
    return ((((65) <= (c)) and ((c) <= (90))) or (((97) <= (c)) and ((c) <= (122)))) and (not(IsVowel(c)))
    # pure-end

def get__closest__vowel(word : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(word)))
    Requires(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(word)))) or ((((65) <= ((word)[i])) and (((word)[i]) <= (90))) or (((97) <= ((word)[i])) and (((word)[i]) <= (122))))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(word)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) <= (1))
    Ensures(not ((len(Result())) == (1)) or (IsVowel((Result())[0])))
    Ensures(not ((len(Result())) == (1)) or (Exists(int, lambda i:
        ((((((1) <= (i)) and (((i) + (1)) < (len(word)))) and (IsVowel((word)[i]))) and (IsConsonant((word)[(i) - (1)]))) and (IsConsonant((word)[(i) + (1)]))) and (
            Forall(int, lambda j:
                not (j > i and j <= len(word) - 2) or (((not(IsVowel((word)[j]))) or (not(IsConsonant((word)[j - 1])))) or (not(IsConsonant((word)[j + 1])))))))))
    # post-conditions-end

    # impl-start
    result : List[int] = list([int(0)] * 0)
    if (len(word)) < (3):
        result = []
        return result
    i : int = (len(word)) - (2)
    while (i) > (0):
        # invariants-start
        Invariant(Acc(list_pred(word)))
        Invariant(Acc(list_pred(result)))
        Invariant(((0) <= (i)) and ((i) <= ((len(word)) - (2))))
        Invariant(Forall(int, lambda j:
            not (((i) < (j)) and ((j) < ((len(word)) - (1)))) or (((not(IsVowel((word)[j]))) or (not(IsConsonant((word)[(j) - (1)])))) or (not(IsConsonant((word)[(j) + (1)]))))))
        Invariant(Forall(int, lambda j:
                not (j > i and j <= len(word) - 2) or (((not(IsVowel((word)[j]))) or (not(IsConsonant((word)[j - 1])))) or (not(IsConsonant((word)[j + 1]))))))
        # invariants-end
        if ((IsVowel((word)[i])) and (IsConsonant((word)[(i) - (1)]))) and (IsConsonant((word)[(i) + (1)])):
            result = [(word)[i]]
            return result
        i = (i) - (1)
    result = []
    return result
    # impl-end
