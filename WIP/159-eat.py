from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def eat(number : int, need : int, remaining : int) -> List[int]:
    Requires((((number) >= (0)) and ((need) >= (0))) and ((remaining) >= (0)))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (2))
    Ensures(not ((remaining) >= (need)) or ((((Result())[0]) == ((number) + (need))) and (((Result())[1]) == ((remaining) - (need)))))
    Ensures(not ((remaining) < (need)) or ((((Result())[0]) == ((number) + (remaining))) and (((Result())[1]) == (0))))
    result = list([int(0)] * 0) # type : List[int]
    if (remaining) < (need):
        result = ([(number) + (remaining), 0])
    else:
        result = ([(number) + (need), (remaining) - (need)])
    return result