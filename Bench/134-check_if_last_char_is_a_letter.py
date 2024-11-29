from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def check__if__last__char__is__a__letter(s : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == ((((len(s)) > (0)) and (is__alpha((s)[(len(s)) - (1)]))) and (((len(s)) == (1)) or (((s)[(len(s)) - (2)]) == (32)))))
    # post-conditions-end

    # impl-start
    b : bool = (((len(s)) > (0)) and (is__alpha((s)[(len(s)) - (1)]))) and (((len(s)) == (1)) or (((s)[(len(s)) - (2)]) == (32)))
    return b
    # impl-end

@Pure
def is__alpha(c : int) -> bool :
    # pure-start
    return (((97) <= (c)) and ((c) <= (122))) or (((65) <= (c)) and ((c) <= (90)))
    # pure-end
