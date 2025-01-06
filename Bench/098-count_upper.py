from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def count__upper__fun(s : List[int], i : int, j : int) -> int:
    # pure-pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(s))))
    # pure-pre-conditions-end
    # pure-post-conditions-start
    Ensures((Result()) >= (0))
    # pure-post-conditions-end

    # pure-start
    if i == j:
        return 0
    else:
        if is__upper__vowel((s)[j - 1]) and (j - 1) % 2 == 0:
            return (1) + (count__upper__fun(s, i, j - 1))
        else:
            return count__upper__fun(s, i, j - 1)
    # pure-end


def count__upper(s : List[int]) -> int:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) >= (0))
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == (count__upper__fun(s, 0, len(s))))
    # post-conditions-end

    # impl-start
    cnt : int = 0
    i : int = 0
    
    while (i) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (i)) and ((i) <= (len(s))))
        Invariant(Forall(int, lambda i: (Implies(i >= 0 and i < len(s), 
            count__upper__fun(s, 0, i + 1) == (count__upper__fun(s, 0, i) + (1) if is__upper__vowel(s[i]) and i % 2 == 0 else count__upper__fun(s, 0, i))), 
                [[count__upper__fun(s, 0, i + 1)]])))
        Invariant((cnt) == (count__upper__fun(s, 0, i)))
        # invariants-end

        # assert-start
        Assert(count__upper__fun(s, 0, i + 1) == (count__upper__fun(s, 0, i) + (1) if is__upper__vowel(s[i]) and i % 2 == 0 else count__upper__fun(s, 0, i)))
        # assert-end
        if (is__upper__vowel((s)[i])) and (((i % 2)) == (0)):
            cnt = (cnt) + (1)
        i = (i) + (1)
    return cnt
    # impl-end

@Pure
def is__upper__vowel(c : int) -> bool :
    # pure-start
    return (((((c) == (0)) or ((c) == (1))) or ((c) == (2))) or ((c) == (3))) or ((c) == (4))
    # pure-end
