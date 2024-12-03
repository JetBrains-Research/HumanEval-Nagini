from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def IsPrime(n : int) -> bool :
    # pure-start
    return ((n) > (1)) and (Forall(int, lambda k:
        Implies(((2) <= (k)) and ((k) < (n)), ((n % k)) != (0))))
    # pure-end

def CountUpTo(n : int) -> List[int]:
    # pre-conditions-start
    Requires((n) >= (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or (((Result())[i]) < (n))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or (IsPrime((Result())[i]))))
    # post-conditions-end

    # impl-start
    primes : List[int] = []
    if (n) <= (2):
        return primes
    i : int = 2
    while (i) < (n):
        # invariants-start
        Invariant(Acc(list_pred(primes)))
        Invariant(((2) <= (i)) and ((i) <= (n)))
        Invariant(Forall(int, lambda x: 
            Implies(x >= 0 and x < len(primes), 2 <= primes[x] and primes[x] < n)))
        Invariant(Forall(int, lambda j:
            (Implies(((0) <= (j)) and ((j) < (len(primes))), IsPrime((primes)[j])), [[IsPrime((primes)[j])]])))
        # invariants-end
        if IsPrime(i):
            primes = primes + [(i)]
        i = (i) + (1)
    return primes
    # impl-end
