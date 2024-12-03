from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def smallest__change__fun(s : List[int], i : int, j : int) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(s) // 2)))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) >= (0))
    # post-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        if (s)[j - 1] != (s)[len(s) - j]:
            return 1 + (smallest__change__fun(s, i, j - 1))
        else:
            return smallest__change__fun(s, i, j - 1)
    # pure-end

def smallest__change(s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == (smallest__change__fun(s, 0, len(s) // 2)))
    # post-conditions-end

    # impl-start
    c : int = 0
    i : int = 0
    while (i) < ((len(s) // 2)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= ((len(s) // 2))))
        Invariant(Forall(int, lambda i: (Implies(i >= 0 and i < len(s) // 2, smallest__change__fun(s, 0, i + 1) == (smallest__change__fun(s, 0, i) + 1 if (s)[i] != (s)[len(s) - i - 1] else smallest__change__fun(s, 0, i))), [[smallest__change__fun(s, 0, i + 1)]])))
        Invariant(c == smallest__change__fun(s, 0, i))
        # invariants-end

        # assert-start
        Assert(smallest__change__fun(s, 0, i + 1) == (smallest__change__fun(s, 0, i) + 1 if (s)[i] != (s)[len(s) - i - 1] else smallest__change__fun(s, 0, i)))
        # assert-end
        if ((s)[i]) != ((s)[((len(s)) - (1)) - (i)]):
            c = (c) + (1)
        i = (i) + (1)
    return c
    # impl-end
