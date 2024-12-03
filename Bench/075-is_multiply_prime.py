from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def Prime(p : int) -> bool :
    # pure-start
    return ((p) > (1)) and (Forall(int, lambda k:
        not (((1) < (k)) and ((k) < (p))) or (((p % k)) != (0))))
    # pure-end

def is__prime(k : int) -> bool:
    # pre-conditions-start
    Requires((k) >= (2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(not (Result()) or (Forall(int, lambda i:
        not (((2) <= (i)) and ((i) < (k))) or ((k % i) != (0)))))
    Ensures(not (not(Result())) or (Exists(int, lambda j:
        (((2) <= (j)) and ((j) < (k))) and (((k % j)) == (0)))))
    Ensures(Result() == Prime(k))
    # post-conditions-end

    # impl-start
    i : int = 2
    result : bool = True
    while (i) < (k):
        # invariants-start
        Invariant(((2) <= (i)) and ((i) <= (k)))
        Invariant(not (not(result)) or (Exists(int, lambda j:
            (((2) <= (j)) and ((j) < (i))) and (((k % j)) == (0)))))
        Invariant(not (result) or (Forall(int, lambda j:
            not (((2) <= (j)) and ((j) < (i))) or (((k % j)) != (0)))))
        # invariants-end
        if ((k % i)) == (0):
            result = False
        i = (i) + (1)
    return result
    # impl-end

def is__multiply__prime(x : int) -> bool:
    # pre-conditions-start
    Requires((x) > (1))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Implies(Result(), Exists(int, lambda a:
        a< x and 
        ((Prime(a)) and 
        Exists(int, lambda b:
            b < x and 
            (Prime(b)) and
            Exists(int, lambda c:
                (c < x) and (Prime(c)) and ((x) == (((a) * (b)) * (c)))))))))
    Ensures(Implies(not(Result()), Forall(int, lambda i:
        (Implies(1 < i and i < x, 
            Forall(int, lambda j:
                (Implies((1 < j and j < x), 
                    (Forall(int, lambda k:
                        (Implies(1 < k and k < x, 
                            Implies((Prime(i)), Implies((Prime(j)), Implies(Prime(k), ((x) != (((i) * (j) * (k)))))))))))))))))))
    # post-conditions-end

    # impl-start
    a : int = int(2)
    result : bool = False
    while a < x:
        # invariants-start
        Invariant(x >= 2)
        Invariant(a >= 2 and a <= x) 
        Invariant(Implies(result, Exists(int, lambda a:
            a< x and 
            ((Prime(a)) and 
            Exists(int, lambda b:
                b < x and 
                (Prime(b)) and
                Exists(int, lambda c:
                    (c < x) and (Prime(c)) and ((x) == (((a) * (b)) * (c)))))))))
        Invariant(Implies(not(result), Forall(int, lambda i:
            (Implies(1 < i and i < a, 
                Forall(int, lambda j:
                    (Implies((1 < j and j < x), 
                        (Forall(int, lambda k:
                            (Implies(1 < k and k < x, 
                                Implies((Prime(i)), Implies((Prime(j)), Implies(Prime(k), ((x) != (((i) * (j) * (k)))))))), 
                                    [[Prime(k)]])))), 
                        [[Prime(j)]]))), 
                [[Prime(i)]]))))
        # invariants-end
        if is__prime(a):
            b : int = int(2)
            while b < x:
                # invariants-start
                Invariant(x >= 2)   
                Invariant(Prime(a))
                Invariant(a >= 2 and a < x)
                Invariant(b >= 2 and b <= x)
                Invariant(Implies(result, Exists(int, lambda a:
                    a< x and 
                    ((Prime(a)) and 
                    Exists(int, lambda b:
                        b < x and 
                        (Prime(b)) and
                        Exists(int, lambda c:
                            (c < x) and (Prime(c)) and ((x) == (((a) * (b)) * (c)))))))))
                Invariant(Implies(not(result), Forall(int, lambda i:
                    (Implies(1 < i and i < a, 
                        Forall(int, lambda j:
                            (Implies((1 < j and j < x), 
                                (Forall(int, lambda k:
                                    (Implies(1 < k and k < x, 
                                        Implies((Prime(i)), Implies((Prime(j)), Implies(Prime(k), ((x) != (((i) * (j) * (k)))))))), 
                                            [[Prime(k)]])))), 
                                [[Prime(j)]]))), 
                        [[Prime(i)]]))))
                Invariant(Implies(not(result), 
                    Forall(int, lambda j:
                        (Implies((1 < j and j < b), 
                            (Forall(int, lambda k:
                                (Implies(1 < k and k < x, 
                                        Implies((Prime(j)), Implies(Prime(k), (x) != (((a) * (j) * (k)))))), 
                                [[Prime(k)]])))), 
                        [[Prime(j)]]))))
                # invariants-end
                if is__prime(b):
                    c : int = int(2)
                    while c < x:
                        # invariants-start
                        Invariant(x >= 2)
                        Invariant(Prime(a))
                        Invariant(Prime(b))
                        Invariant(a >= 2 and a < x)
                        Invariant(b >= 2 and b < x)
                        Invariant(c >= 2 and c <= x)
                        Invariant(Implies(result, Exists(int, lambda a:
                            a< x and 
                            ((Prime(a)) and 
                            Exists(int, lambda b:
                                b < x and 
                                (Prime(b)) and
                                Exists(int, lambda c:
                                    (c < x) and (Prime(c)) and ((x) == (((a) * (b)) * (c)))))))))
                        Invariant(Implies(not(result), Forall(int, lambda i:
                            (Implies(1 < i and i < a, 
                                Forall(int, lambda j:
                                    (Implies((1 < j and j < x), 
                                        (Forall(int, lambda k:
                                            (Implies(1 < k and k < x, 
                                                Implies((Prime(i)), Implies((Prime(j)), Implies(Prime(k), ((x) != (((i) * (j) * (k)))))))), 
                                                    [[Prime(k)]])))), 
                                        [[Prime(j)]]))), 
                                [[Prime(i)]]))))
                        Invariant(Implies(not(result), 
                            Forall(int, lambda j:
                                (Implies((1 < j and j < b), 
                                    (Forall(int, lambda k:
                                        (Implies(1 < k and k < x, 
                                                Implies((Prime(j)), Implies(Prime(k), (x) != (((a) * (j) * (k)))))), 
                                        [[Prime(k)]])))), 
                                [[Prime(j)]]))))
                        Invariant(Implies(not(result), 
                            Forall(int, lambda k: 
                                (Implies(1 < k and k < c, 
                                    Implies((Prime(k)), ((x) != (((a) * (b) * (k)))))), 
                                [[Prime(k)]]))))
                        # invariants-end
                        if (is__prime(c)) and ((x) == (((a) * (b)) * (c))):
                            result = True
                        c = c + 1
                b = b + 1
        a = a + 1
    return result
    # impl-end
