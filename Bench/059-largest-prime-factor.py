from nagini_contracts.contracts import *

def is_prime(k : int) -> bool:
    # pre-conditions-start
    Requires(k >= 2)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Implies(Result(), Forall(int, lambda i : Implies((i >= 2) and (i < k), (k % i != 0)))))
    Ensures(Implies(Result() == False, Exists(int, lambda j : ((j >= 2) and (j < k) and (k % j == 0)))))
    # post-conditions-end

    # impl-start
    i : int = 2
    result : bool = True
    while i < k:
        # invariants-start
        Invariant(i >= 2 and i <= k)
        Invariant(Implies(result == False, Exists(int, lambda j : ((j >= 2) and (j < i) and (k % j == 0)))))
        Invariant(Implies(result, Forall(int, lambda j : Implies((j >= 2) and (j < i), (k % j != 0)))))
        # invariants-end
        if k % i == 0:
            result = False
        i = i + 1
    return result
    # impl-end

@Pure
def is_prime_pred(k : int) -> bool:
    # pure-start
    return Forall(int, lambda i : Implies((i >= 2) and (i < k), (k % i != 0)))
    # pure-end

def largest_prime_factor(n: int) -> int:
    # pre-conditions-start
    Requires(n >= 2)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() >= 1 and Result() <= n and (Result() == 1 or Result() > 1 and is_prime_pred(Result())))
    # post-conditions-end

    # impl-start
    largest : int = 1
    j : int = 2
    while j <= n:
        # invariants-start
        Invariant(j >= 2 and j <= n + 1)
        Invariant(largest >= 1 and largest < j)
        Invariant(largest == 1 or largest > 1 and is_prime_pred(largest))
        # invariants-end
        if n % j == 0 and is_prime(j):
            largest = max(largest, j)
        j = j + 1
    return largest
    # impl-end
