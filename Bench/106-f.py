from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def factorial__spec(n : int) -> int :
    # pre-conditions-start
    Requires(n >= -1)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() >= 0)
    # post-conditions-end

    # pure-start
    if n == -1:
        return 1
    else:
        return (n + 1) * factorial__spec(n - 1)
    # pure-end

@Pure
def sum__spec(n : int) -> int :
    # pre-conditions-start
    Requires(n >= -1)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() >= 0)
    # post-conditions-end

    # pure-start
    if 0 > n:
        return 0
    else:
        return n + 1 + sum__spec(n - 1)
    # pure-end

def f(n : int) -> List[int]:
    # pre-conditions-start
    Requires((n) >= (1))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == (n))
    Ensures(Forall(int, lambda i:
        not ((((i) >= (0)) and ((i) < (len(Result())))) and (((i % 2)) == (0))) or (((Result())[i]) == (factorial__spec(i - 1)))))
    Ensures(Forall(int, lambda i:
        not ((((i) >= (0)) and ((i) < (len(Result())))) and (((i % 2)) != (0))) or (((Result())[i]) == (sum__spec(i - 1)))))
    # post-conditions-end
    
    # impl-start
    result : List[int] = []
    i : int = 0
    while (i) < (n):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(((i) >= (0)) and ((i) <= (n)))
        Invariant((len(result)) == (i))
        Invariant(Forall(int, lambda i:
            (Implies((((i) >= (0)) and ((i) < (len(result)))) and (((i % 2)) == (0)), ((result)[i]) == (factorial__spec(i - 1))), [[factorial__spec(i - 1)]])))
        Invariant(Forall(int, lambda i:
            (Implies((((i) >= (0)) and ((i) < (len(result)))) and (((i % 2)) != (0)), ((result)[i]) == (sum__spec(i - 1))), [[sum__spec(i - 1)]])))
        # invariants-end
        if ((i % 2)) == (0):
            x : int = 1
            j : int = 0
            while (j) < (i):
                # invariants-start
                Invariant(Acc(list_pred(result)))
                Invariant(((i) >= (0)) and ((i) <= (n)))
                Invariant((len(result)) == (i))
                Invariant(((j) >= (0)) and ((j) <= (i)))
                Invariant((x) == (factorial__spec(j - 1)))
                Invariant(Forall(int, lambda i:
                    (Implies((((i) >= (0)) and ((i) < (len(result)))) and (((i % 2)) == (0)), ((result)[i]) == (factorial__spec(i - 1))), [[factorial__spec(i - 1)]])))
                Invariant(Forall(int, lambda i:
                    (Implies((((i) >= (0)) and ((i) < (len(result)))) and (((i % 2)) != (0)), ((result)[i]) == (sum__spec(i - 1))), [[sum__spec(i - 1)]])))
                # invariants-end
                x = (x) * (j + 1)
                j = (j) + (1)
            result = (result) + [x]
        else:
            x : int = 0
            j : int = 0
            while (j) < (i):
                # invariants-start
                Invariant(Acc(list_pred(result)))
                Invariant(((i) >= (0)) and ((i) <= (n)))
                Invariant((len(result)) == (i))
                Invariant(((j) >= (0)) and ((j) <= (i)))
                Invariant((x) == (sum__spec(j - 1)))
                Invariant(Forall(int, lambda i:
                    (Implies((((i) >= (0)) and ((i) < (len(result)))) and (((i % 2)) == (0)), ((result)[i]) == (factorial__spec(i - 1))), [[factorial__spec(i - 1)]])))
                Invariant(Forall(int, lambda i:
                    (Implies((((i) >= (0)) and ((i) < (len(result)))) and (((i % 2)) != (0)), ((result)[i]) == (sum__spec(i - 1))), [[sum__spec(i - 1)]])))
                # invariants-end
                x = (x) + (j + 1)
                j = (j) + (1)
            result = (result) + [x]
        i = (i) + (1)
    return result
    # impl-end
