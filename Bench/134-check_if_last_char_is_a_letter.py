from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def check__if__last__char__is__a__letter(s : List[int]) -> bool:
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(s)))
    Ensures((Result()) == ((((len(s)) > (0)) and (is__alpha((s)[(len(s)) - (1)]))) and (((len(s)) == (1)) or (((s)[(len(s)) - (2)]) == (32)))))
    b = False # type : bool
    b = (((len(s)) > (0)) and (is__alpha((s)[(len(s)) - (1)]))) and (((len(s)) == (1)) or (((s)[(len(s)) - (2)]) == (32)))
    return b

@Pure
def is__alpha(c : int) -> bool :
    return (((97) <= (c)) and ((c) <= (122))) or (((65) <= (c)) and ((c) <= (90)))
