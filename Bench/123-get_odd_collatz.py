from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure 
def iterate__to__odd(n : int) -> int :
    # pre-conditions-start
    Requires(n % 2 == 0)
    Requires(n >= 0)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() % 2 == 1)
    Ensures(Result() > 0)
    # post-conditions-end

    # pure-start
    if (n // 2) % 2 == 1:
        return n // 2
    else:
        return iterate__to__odd(n // 2)
    # pure-end

@Pure
def next__odd__collatz(n : int) -> int :
    # pre-conditions-start
    Requires(n > 0)
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() > 0)
    Ensures(Result() % 2 == 1)
    # post-conditions-end

    # pure-start
    if ((n % 2)) == (0):
        return iterate__to__odd(n)
    else:
        return iterate__to__odd(((3) * (n)) + (1))
    # pure-end

def next__odd__collatz__iter(n : int) -> int:
    # pre-conditions-start
    Requires((n) > (0))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Result() > 0)
    Ensures(((Result() % 2)) == (1))
    Ensures((Result()) == (next__odd__collatz(n)))
    # post-conditions-end

    # impl-start
    next : int = n
    if ((next % 2)) == (1):
        next = ((3) * (next)) + (1)
    start : int = next
    while ((next % 2)) == (0):
        # invariants-start
        Invariant((next) > (0))
        Invariant(not (((next % 2)) == (0)) or ((next__odd__collatz(next)) == (next__odd__collatz(n))))
        Invariant(not (((next % 2)) == (0)) or ((iterate__to__odd(next)) == (iterate__to__odd(start))))
        Invariant(not (((next % 2)) == (1)) or ((next) == (iterate__to__odd(start))))
        # invariants-end
        next = (next // 2)
    return next
    # impl-end


def get__odd__collatz__unsorted(n : int) -> List[int]:
    # pre-conditions-start
    Requires((n) > (1))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or ((((Result())[i] > 0)))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or ((((Result())[i] % 2)) == (1))))
    Ensures(Forall(int, lambda i:
        not (((1) <= (i)) and ((i) < (len(Result())))) or (((Result())[i]) == (next__odd__collatz((Result())[(i) - (1)])))))
    # post-conditions-end
    # impl-start
    odd__collatz : List[int] = []
    cur : int = n
    if ((cur % 2)) == (0):
        cur = next__odd__collatz__iter(cur)
    odd__collatz = [cur]
    # assert-start
    Assert(len(odd__collatz) == 1)
    Assert(Forall(int, lambda i:
        (not (((1) <= (i)) and ((i) < (len(odd__collatz)))))))
    Assert(Forall(int, lambda i:
        (not (((1) <= (i)) and ((i) < (len(odd__collatz)))) or (((odd__collatz)[i]) == (next__odd__collatz((odd__collatz)[(i) - (1)]))), [[next__odd__collatz((odd__collatz)[(i) - (1)])]])))
    # assert-end
    while ((odd__collatz)[(len(odd__collatz)) - (1)]) != (1):
        # invariants-start
        Invariant(Acc(list_pred(odd__collatz)))
        Invariant((cur) > (0))
        Invariant((len(odd__collatz)) > (0))
        Invariant(Forall(int, lambda i:
            (not (((0) <= (i)) and ((i) < (len(odd__collatz)))) or ((((odd__collatz)[i] > 0))))))
        Invariant(Forall(int, lambda i:
            (not (((0) <= (i)) and ((i) < (len(odd__collatz)))) or ((((odd__collatz)[i] % 2)) == (1)))))
        Invariant(Forall(int, lambda i:
            (not (((1) <= (i)) and ((i) < (len(odd__collatz)))) or (((odd__collatz)[i]) == (next__odd__collatz((odd__collatz)[(i) - (1)]))), [[next__odd__collatz((odd__collatz)[(i) - (1)])]])))
        # invariants-end
        odd__collatz = (odd__collatz) + [next__odd__collatz__iter((odd__collatz)[(len(odd__collatz)) - (1)])]
        # assert-start
        Assert(Forall(int, lambda i:
            (not (((1) <= (i)) and ((i) < (len(odd__collatz)))) or (((odd__collatz)[i]) == (next__odd__collatz((odd__collatz)[(i) - (1)]))), [[next__odd__collatz((odd__collatz)[(i) - (1)])]])))
        # assert-end
    return odd__collatz
    # impl-end



def get__odd__collatz(n : int) -> List[int]:
    # pre-conditions-start
    Requires((n) > (1))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda i:
        Forall(int, lambda j:
            not ((((0) <= (i)) and ((i) < (j))) and ((j) < (len(Result())))) or (((Result())[i]) <= ((Result())[j])))))
    Ensures(Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(Result())))) or ((((Result())[i] % 2)) == (1))))
    # post-conditions-end

    # impl-start
    sorted : List[int] = []
    sorted = get__odd__collatz__unsorted(n)
    unsorted : List[int] = list(sorted)
    i : int = 0
    while (i) < (len(sorted)):
        # invariants-start
        Invariant(Acc(list_pred(sorted)))
        Invariant(Acc(list_pred(unsorted)))
        Invariant(((0) <= (i)) and ((i) <= (len(sorted))))
        Invariant(Forall(int, lambda i:
            not (((0) <= (i)) and ((i) < (len(sorted)))) or ((((sorted)[i] % 2)) == (1))))
        Invariant((len(sorted)) == (len(unsorted)))
        Invariant(Forall(int, lambda j:
            (Forall(int, lambda k:
                (not ((((0) <= (j)) and ((j) < (k))) and ((k) < (i))) or (((sorted)[j]) <= ((sorted)[k])), 
                    [[(sorted)[k]]])), 
                [[sorted[j]]])))
        Invariant(Forall(int, lambda j:
            (not ((((0) <= (j)) and ((j) < (i)))) or 
                (Forall(int, lambda k:
                    (not ((((i) <= (k)) and ((k) < (len(sorted))))) or 
                        (((sorted)[j]) <= ((sorted)[k])), [[sorted[k]]]))), [[(sorted)[j]]])))
        # invariants-end
        minIndex : int = i
        j : int = (i) + (1)
        while (j) < (len(sorted)):
            # invariants-start
            Invariant(Acc(list_pred(sorted)))
            Invariant(Acc(list_pred(unsorted)))
            Invariant((len(sorted)) == (len(unsorted)))
            Invariant(((0) <= (i)) and ((i) < (len(sorted))))
            Invariant((((i) <= (minIndex)) and ((minIndex) < (j))) and ((j) <= (len(sorted))))
            Invariant(Forall(int, lambda i:
                not (((0) <= (i)) and ((i) < (len(sorted)))) or ((((sorted)[i] % 2)) == (1))))
            Invariant(Forall(int, lambda j:
                (Forall(int, lambda k:
                    (not ((((0) <= (j)) and ((j) < (k))) and ((k) < (i))) or (((sorted)[j]) <= ((sorted)[k])), 
                        [[(sorted)[k]]])), 
                    [[sorted[j]]])))
            Invariant(Forall(int, lambda j:
                (not ((((0) <= (j)) and ((j) < (i)))) or 
                    (Forall(int, lambda k:
                        (not ((((i) <= (k)) and ((k) < (len(sorted))))) or 
                            (((sorted)[j]) <= ((sorted)[k])), [[sorted[k]]]))), [[(sorted)[j]]])))
            Invariant(Forall(int, lambda k:
                (not (((i) <= (k)) and ((k) < (j))) or (((sorted)[minIndex]) <= ((sorted)[k])), [[(sorted)[k]]])))
            # invariants-end
            if ((sorted)[j]) < ((sorted)[minIndex]):
                minIndex = j
            j = (j) + (1)
        if (minIndex) != (i):
            rhs0_ : int = (sorted)[i]
            (sorted)[i] = (sorted)[minIndex]
            (sorted)[minIndex] = rhs0_
        i = (i) + (1)
    return sorted
    # impl-end

