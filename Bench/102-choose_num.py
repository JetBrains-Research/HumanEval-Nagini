from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def choose__num(x : int, y : int) -> int:
    # pre-conditions-start
    Requires(((0) <= (x)) and ((0) <= (y)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(((Result()) == (-1)) or (((Result()) >= (x)) and ((Result()) <= (y))))
    Ensures(((Result()) == (-1)) or (((Result() % 2)) == (0)))
    Ensures(((Result()) == (-1)) or (Forall(int, lambda i:
        not ((((x) <= (i)) and ((i) <= (y))) and (((i % 2)) == (0))) or ((Result()) >= (i)))))
    Ensures(((Result()) == (-1)) == ((x) >= (y)))
    # post-conditions-end

    # impl-start
    num : int = -1
    if (x) >= (y):
        return num
    if ((x % 2)) == (0):
        num = x
    elif True:
        num = (x) + (1)
    i : int = (x) + (2)
    while (i) <= (y):
        # invariants-start
        Invariant(((i) >= (x)) and ((i) <= ((y) + (1))))
        Invariant(((num) == (-1)) or (((num % 2)) == (0)))
        Invariant(Forall(int, lambda j:
            not ((((x) <= (j)) and ((j) < (i))) and (((j % 2)) == (0))) or ((num) >= (j))))
        Invariant(((num) == (-1)) or (((num) >= (x)) and ((num) < (i))))
        # invariants-end
        if ((i % 2)) == (0):
            num = i
        i = (i) + (1)
    return num
    # impl-end
