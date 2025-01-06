from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def will__it__fly(s : List[int], w : int) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires((len(s)) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == ((is__palindrome__pred(s)) and ((psum(0, len(s), s)) <= (w))))
    # post-conditions-end

    # impl-start
    result : bool = True
    i : int = 0
    j : int = (len(s)) - (1)
    while (i) < (j):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) < (len(s))))
        Invariant(((0) <= (j)) and ((j) < (len(s))))
        Invariant((j) == (((len(s)) - (i)) - (1)))
        Invariant(Forall(int, lambda k:
            not (((0) <= (k)) and ((k) < (i))) or (((s)[k]) == ((s)[((len(s)) - (1)) - (k)]))))
        # invariants-end
        if ((s)[i]) != ((s)[j]):
            result = False
            return result
        i = (i) + (1)
        j = (j) - (1)
    total : int = 0
    i = 0
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant(Forall(int, lambda i: (not (((0) <= (i)) and ((i) < (len(s)))) or ((psum(0, i + 1, s)) == (psum(0, i, s) + s[i])), [[psum(0, i + 1, s)]])))
        Invariant((total) == (psum(0, i, s)))
        Invariant(Forall(int, lambda k:
            not (((0) <= (k)) and ((k) < (len(s)))) or (((s)[k]) == ((s)[((len(s)) - (1)) - (k)]))))
        # invariants-end

        # assert-start
        Assert((psum(0, (i) + (1), s)) == ((psum(0, i, s) + (s)[i])))
        # assert-end
        total = (total) + ((s)[i])
        i = (i) + (1)
    return (total) <= (w)
    # impl-end

@Pure
def is__palindrome__pred(s : List[int]) -> bool :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pure-pre-conditions-end

    # pure-start
    return Forall(int, lambda k:
        not (((0) <= (k)) and ((k) < (len(s)))) or (((s)[k]) == ((s)[((len(s)) - (1)) - (k)])))
    # pure-end

@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pure-pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return (s)[j - 1] + (psum(i, j - 1, s))
    # pure-end
