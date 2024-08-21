from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def IsEven(n : int) -> bool:
    Ensures(((Result()) == (True)) or ((Result()) == (False)))
    return (n % 2) == 0

@Pure
def CountEvens(i : int, lst : List[int]) -> int:
    Requires(Acc(list_pred(lst)))
    Requires(((i) >= (0)) and ((i) <= (len(lst))))
    Ensures((Result()) >= (0))
    Ensures((Result()) <= (len(lst) - i))
    if len(lst) == i:
        return 0
    return CountEvens(i + 1, lst) + IsEven(lst[i])

def Exchange(lst1 : List[int], lst2 : List[int]) -> str:
    Requires(Acc(list_pred(lst2)))
    Requires(Acc(list_pred(lst1)))
    Requires(((len(lst1)) > (0)) and ((len(lst2)) > (0)))
    Ensures(Acc(list_pred(lst2)))
    Ensures(Acc(list_pred(lst1)))
    Ensures(((Result()) == "YES") or ((Result()) == "NO"))
    Ensures(not ((Result()) == "YES") or (((CountEvens(0, lst1)) + (CountEvens(0, lst2))) >= (len(lst1))))
    Ensures(not ((Result()) == "NO") or (((CountEvens(0, lst1)) + (CountEvens(0, lst2))) < (len(lst1))))
    result = "" # type : str
    d_1_totalEvens_ = int(0) # type : int
    d_1_totalEvens_ = CountEvens(0, lst1) + CountEvens(0, lst2)
    if (d_1_totalEvens_) >= (len(lst1)):
        result = "YES"
    elif True:
        result = "NO"
    return result
