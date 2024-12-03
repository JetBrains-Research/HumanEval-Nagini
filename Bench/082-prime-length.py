from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def is__prime(s : str) -> bool:
    # pre-conditions-start
    Requires((len(s)) >= (2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(not (Result()) or (Forall(int, lambda i:
        not (((2) <= (i)) and ((i) < (len(s)))) or ((len(s) % i) != (0)))))
    Ensures(not (not(Result())) or (Exists(int, lambda j:
        (((2) <= (j)) and ((j) < (len(s)))) and (((len(s) % j)) == (0)))))
    # post-conditions-end

    # impl-start
    i : int = 2
    result : bool = True
    while (i) < (len(s)):
        # invariants-start
        Invariant(((2) <= (i)) and ((i) <= (len(s))))
        Invariant(not (not(result)) or (Exists(int, lambda j:
            (((2) <= (j)) and ((j) < (i))) and (((len(s) % j)) == (0)))))
        Invariant(not (result) or (Forall(int, lambda j:
            not (((2) <= (j)) and ((j) < (i))) or (((len(s) % j)) != (0)))))
        # invariants-end
        if ((len(s) % i)) == (0):
            result = False
        i = (i) + (1)
    return result
    # impl-end
