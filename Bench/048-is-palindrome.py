from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def is__palindrome(text : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(text)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(text)))
    Ensures((Result()) == (Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(text)))) or (((text)[i]) == ((text)[((len(text)) - (i)) - (1)])))))
    # post-conditions-end

    # impl-start
    result : bool = True
    i : int = 0
    while (i) < ((len(text) // 2)):
        # invariants-start
        Invariant(Acc(list_pred(text)))
        Invariant(((0) <= (i)) and ((i) <= ((len(text) // 2))))
        Invariant((result) == (Forall(int, lambda i1:
            not (((i1) >= (0)) and ((i1) < (i))) or (((text)[i1]) == ((text)[((len(text)) - (i1)) - (1)])))))
        # invariants-end
        if ((text)[i]) != ((text)[((len(text)) - (i)) - (1)]):
            result = False
        i = (i) + (1)
    return result
    # impl-end
