from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def is__palindrome(text : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(text)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(text)))
    Ensures((Result()) == (Forall(int, lambda d_0_i_:
        not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(text)))) or (((text)[d_0_i_]) == ((text)[((len(text)) - (d_0_i_)) - (1)])))))
    # post-conditions-end

    # impl-start
    result = False # type : bool
    result = True
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    while (d_1_i_) < ((len(text) // 2)):
        # invariants-start
        Invariant(Acc(list_pred(text)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= ((len(text) // 2))))
        Invariant((result) == (Forall(int, lambda d_2_i1_:
            not (((d_2_i1_) >= (0)) and ((d_2_i1_) < (d_1_i_))) or (((text)[d_2_i1_]) == ((text)[((len(text)) - (d_2_i1_)) - (1)])))))
        # invariants-end
        if ((text)[d_1_i_]) != ((text)[((len(text)) - (d_1_i_)) - (1)]):
            result = False
        d_1_i_ = (d_1_i_) + (1)
    return result
    # impl-end
