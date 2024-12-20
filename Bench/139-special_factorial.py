from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def factorial(n : int) -> int :
    # pure-pre-conditions-start
    Requires((n) >= (0))
    # pure-pre-conditions-end
    # pure-post-conditions-start
    Ensures((Result()) >= (0))
    # pure-post-conditions-end

    # pure-start
    if (n) == (0):
        return 1
    else:
        return (n) * (factorial((n) - (1)))
    # pure-end

@Pure
def special__factorial__rec(n : int) -> int :
    # pure-pre-conditions-start
    Requires((n) >= (0))
    # pure-pre-conditions-end
    # pure-post-conditions-start
    Ensures((Result()) >= (0))
    # pure-post-conditions-end

    # pure-start
    if (n) == (0):
        return 1
    else:
        return factorial(n) * (special__factorial__rec((n) - (1)))
    # pure-end

def special__factorial(n : int) -> int:
    # pre-conditions-start
    Requires((n) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) == (special__factorial__rec(n)))
    # post-conditions-end

    # impl-start
    result : int = 1
    fact : int = 1
    i : int = 1
    while (i) <= (n):
        # invariants-start
        Invariant(((1) <= (i)) and ((i) <= (n + 1)))
        Invariant(Forall(int, lambda i: (not (((0) <= (i)) and ((i) <= (n))) or ((factorial(i + 1)) == (factorial(i) * (i + 1))), [[factorial(i + 1)]])))
        Invariant(Forall(int, lambda i: (not (((0) <= (i)) and ((i) <= (n))) or ((special__factorial__rec(i + 1)) == (special__factorial__rec(i) * factorial(i + 1))), [[special__factorial__rec(i + 1)]])))
        Invariant((result) == (special__factorial__rec(i - 1)))
        Invariant((fact) == (factorial(i - 1)))
        # invariants-end
        fact = (fact) * (i)
        result = (result) * (fact)
        i = (i) + (1)
    return result
    # impl-end
