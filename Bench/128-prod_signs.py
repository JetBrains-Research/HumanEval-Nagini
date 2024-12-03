from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def abs(x : int) -> int :
    # pure-start
    if (x) >= (0):
        return x
    elif True:
        return (0) - (x)
    # pure-end

@Pure
def sum__abs(i : int, j : int, s : List[int]) -> int :
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return abs(s[j - 1]) + sum__abs(i, j - 1, s)
    # pure-end
    
@Pure 
def count_negatives(i : int, j : int, s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(0 <= i and i <= j and j <= len(s))
    # pre-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        return (1 if s[j - 1] < 0 else 0) + count_negatives(i, j - 1, s)
    # pure-end

def prod__signs(numbers : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(numbers)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(numbers)))
    Ensures((abs(Result())) == (sum__abs(0, len(numbers), numbers)))
    Ensures(Implies(count_negatives(0, len(numbers), numbers) % 2 == 1, Result() <= 0))
    Ensures(Implies(count_negatives(0, len(numbers), numbers) % 2 == 0, Result() >= 0))
    # post-conditions-end

    # impl-start
    s : int = 0
    i : int = 0
    while (i) < (len(numbers)):
        # invariants-start
        Invariant(Acc(list_pred(numbers)))
        Invariant(((0) <= (i)) and ((i) <= (len(numbers))))
        Invariant(Forall(int, lambda x : 
            (Implies(0 <= x and x < len(numbers), sum__abs(0, x + 1, numbers) == sum__abs(0, x, numbers) + abs(numbers[x])), 
                [[sum__abs(0, x + 1, numbers)]])))
        Invariant((s) == (sum__abs(0, i, numbers)))
        Invariant(s >= 0)
        # invariants-end

        # assert-start
        Assert(sum__abs(0, i + 1, numbers) == sum__abs(0, i, numbers) + abs(numbers[i]))
        # assert-end
        s = (s) + (abs((numbers)[i]))
        i = (i) + (1)
    i = 0
    cnt : int = 0
    while (i) < (len(numbers)):
        # invariants-start
        Invariant(Acc(list_pred(numbers)))
        Invariant(s == sum__abs(0, len(numbers), numbers))
        Invariant(s >= 0)
        Invariant(((0) <= (i)) and ((i) <= (len(numbers))))
        Invariant(Forall(int, lambda x : Implies(0 <= x and x < len(numbers), count_negatives(0, x + 1, numbers) == count_negatives(0, x, numbers) + (1 if numbers[x] < 0 else 0))))
        Invariant((cnt) == (count_negatives(0, i, numbers)))
        # invariants-end
        if ((numbers)[i]) < (0):
            cnt = (cnt) + (1)
        i = (i) + (1)
    if ((cnt % 2)) == (1):
        s = (0) - (s)
    return s
    # impl-end
