from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def car__race__collision(n : int) -> int:
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures((Result()) == ((n) * (n)))
    # post-conditions-end

    # impl-start
    cnt = int(0) # type : int
    cnt = (n) * (n)
    return cnt
    # impl-end
