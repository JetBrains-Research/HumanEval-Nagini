from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

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

@Pure
def prod(i : int, j : int, s : List[int]) -> int :
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pure-pre-conditions-end

    # pure-start
    if i == j:
        return 1
    else:
        return (s)[j - 1] * (prod(i, j - 1, s))
    # pure-end

def sum__product(numbers : List[int]) -> Tuple[int, int]:
    # pre-conditions-start
    Requires(Acc(list_pred(numbers)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(numbers)))
    Ensures((Result()[0]) == (psum(0, len(numbers), numbers)))
    Ensures((Result()[1]) == (prod(0, len(numbers), numbers)))
    # post-conditions-end

    # impl-start
    s : int = 0
    p : int = 1
    i : int = 0
    while (i) < (len(numbers)):
        # invariants-start
        Invariant(Acc(list_pred(numbers)))
        Invariant(((0) <= (i)) and ((i) <= (len(numbers))))
        Invariant((s) == (psum(0, i, numbers)))
        Invariant(Forall(int, lambda i: (not (((0) <= (i)) and ((i) < (len(numbers)))) or ((psum(0, i + 1, numbers)) == (psum(0, i, numbers) + numbers[i])), [[psum(0, i + 1, numbers)]])))
        Invariant(Forall(int, lambda i: (not (((0) <= (i)) and ((i) < (len(numbers)))) or ((prod(0, i + 1, numbers)) == (prod(0, i, numbers) * numbers[i])), [[prod(0, i + 1, numbers)]])))
        Invariant((p) == (prod(0, i, numbers)))
        # invariants-end

        # assert-start
        Assert((psum(0, (i) + (1), numbers)) == ((psum(0, i, numbers) + (numbers)[i])))
        # assert-end
        s = (s) + ((numbers)[i])
        # assert-start
        Assert((prod(0, i + 1, numbers)) == ((prod(0, i, numbers)) * ((numbers)[i])))
        # assert-end
        p = (p) * ((numbers)[i])
        i = (i) + (1)
    return s, p
    # impl-end
