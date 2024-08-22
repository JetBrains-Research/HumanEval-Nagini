from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def is__equal__to__sum__even(n : int) -> bool:
    Ensures((Result()) == ((((n % 2)) == (0)) and ((n) >= (8))))
    b = False # type : bool
    b = (((n % 2)) == (0)) and ((n) >= (8))
    return b
