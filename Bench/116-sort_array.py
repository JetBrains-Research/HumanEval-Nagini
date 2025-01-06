from typing import List, Tuple
from nagini_contracts.contracts import *

@Pure 
def popcount(n : int) -> int :
    # pure-pre-conditions-start
    Requires(n >= 0)
    # pure-pre-conditions-end

    # pure-start
    if n == 0:
        return 0
    else:
        return ((n % 2)) + popcount(n // 10)
    # pure-end

def BubbleSort(a1 : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(a1), 1/2))
    Requires(Forall(int, lambda i : Implies(i >= 0 and i < len(a1), a1[i] >= 0)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(a1), 1/2))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(a1)) == (len(Result())))
    Ensures(Forall(int, lambda i : Implies(i >= 0 and i < len(Result()), Result()[i] >= 0)))
    Ensures(Forall(int, lambda i:
        Forall(int, lambda j:
            Implies((((0) <= (i)) and ((i) < (j))) and ((j) < (len((Result())))), popcount((Result())[i]) <= popcount((Result())[j])))))
    # post-conditions-end

    # impl-start
    a : List[int] = list(a1)
    i : int = (len((a))) - (1)
    while (i) > (0):
        # invariants-start
        Invariant(Acc(list_pred(a)))
        Invariant(Forall(int, lambda i : Implies(i >= 0 and i < len(a), a[i] >= 0)))
        Invariant(Acc(list_pred(a1), 1/2))
        Invariant((len(a1)) == (len(a)))
        Invariant(not ((i) < (0)) or ((len((a))) == (0)))
        Invariant(((-1) <= (i)) and ((i) < (len((a)))))
        Invariant(Forall(int, lambda ii:
            (Forall(int, lambda jj:
                (Implies((((i) <= (ii)) and ((ii) < (jj))) and ((jj) < (len((a)))), popcount((a)[ii]) <= popcount((a)[jj])),
                    [[popcount((a)[jj])]])),
                [[popcount((a)[ii])]])))
        Invariant(Forall(int, lambda k:
            (Forall(int, lambda k_k:
                (Implies(((((0) <= (k)) and ((k) <= (i))) and ((i) < (k_k)) and (k_k) < (len((a)))), popcount((a)[k]) <= popcount((a)[k_k])),
                    [[popcount((a)[k_k])]])),
                [[popcount((a)[k])]])))
        # invariants-end
        j : int = 0
        while (j) < (i):
            # invariants-start
            Invariant(Acc(list_pred(a)))
            Invariant(Forall(int, lambda i : Implies(i >= 0 and i < len(a), a[i] >= 0)))
            Invariant(Acc(list_pred(a1), 1/2))
            Invariant((len(a1)) == (len(a)))
            Invariant((((0) < (i)) and ((i) < (len((a))))) and (((0) <= (j)) and ((j) <= (i))))
            Invariant(Forall(int, lambda ii:
                (Forall(int, lambda jj:
                    (Implies((((i) <= (ii)) and ((ii) <= (jj))) and ((jj) < (len((a)))), popcount((a)[ii]) <= popcount((a)[jj])),
                        [[popcount((a)[jj])]])),
                    [[popcount((a)[ii])]])))
            Invariant(Forall(int, lambda k:
                (Forall(int, lambda k_k:
                    (Implies(((((0) <= (k)) and ((k) <= (i))) and ((i) < (k_k))) and ((k_k) < (len((a)))), popcount((a)[k]) <= popcount((a)[k_k])),
                        [[popcount((a)[k_k])]])),
                    [[popcount((a)[k])]])))
            Invariant(Forall(int, lambda k:
                (Implies(((0) <= (k)) and ((k) <= (j)), popcount((a)[k]) <= popcount((a)[j])),
                    [[popcount((a)[k])]])))
            # invariants-end
            if popcount((a)[j]) > popcount((a)[(j) + (1)]):
                rhs0_ : int = (a)[(j) + (1)]
                (a)[(j) + (1)] = (a)[j]
                (a)[j] = rhs0_
                # assert-start
                Assert(popcount((a)[j]) <= popcount((a)[(j) + (1)]))
                # assert-end
            j = (j) + (1)
        i = (i) - (1)
    return a
    # impl-end
