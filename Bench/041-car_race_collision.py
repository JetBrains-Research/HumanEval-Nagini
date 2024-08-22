from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def car__race__collision(n : int) -> int:
    Requires((n) >= (0))
    Ensures((Result()) == ((n) * (n)))
    cnt = int(0) # type : int
    cnt = (n) * (n)
    return cnt
