from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

@Pure
def tri(n : int) -> int :
    Requires((n) >= (0))
    if (n) == (1):
        return 3
    elif ((n % 2)) == (0):
        return (1) + ((n // 2))
    elif True:
        return ((tri((n) - (2)))) + (tri((n) - (1))) + (tri((n) + (1)))

def Tribonacci(n : int) -> List[int]:
    Requires((n) >= (0))
    Ensures(Acc(list_pred(Result())))
    Ensures((len(Result())) == ((n) + (1)))
    Ensures(Forall(int, lambda d_0_i_:
        Implies(((0) <= (d_0_i_)) and ((d_0_i_) <= (n)), ((Result())[d_0_i_]) == (tri(d_0_i_)))))
    result = list([int(0)] * (n + 1)) # type : List[int]
    result[0] = 1
    Assert(result[0] == tri(0))
    if (n) > 0:
        result[1] = 3
        d_1_i_ = int(0) # type : int
        d_1_i_ = 2
        Assert(result[1] == tri(1))
        Assert(result[(d_1_i_) - (2)] == tri(d_1_i_ - 2))
        Assert(result[(d_1_i_) - (1)] == tri(d_1_i_ - 1))
        Assert(Forall(int, lambda d_2_j_:
            (Implies(((0) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_)), ((result)[d_2_j_]) == (tri(d_2_j_))))))
        while (d_1_i_) <= (n):
            Invariant(Acc(list_pred(result)))
            Invariant(n >= 1)
            Invariant(((2) <= (d_1_i_)) and ((d_1_i_) <= ((n) + (1))))
            Invariant((len(result)) == (n + 1))
            Invariant(Forall(int, lambda x: (Implies(0 <= x and x <= n, tri(x) == (3 if x == 1 else ((1 + (x // 2)) if x % 2 == 0 else tri(x - 1) + tri(x - 2) + tri(x + 1)))), [[tri(x)]])))
            Invariant(Forall(int, lambda x: (Implies(2 <= x and x <= n and x % 2 == 1, (x + 1) % 2 == 0 and tri(x + 1) == (x + 3) // 2), [[tri(x + 1)]])))
            Invariant(Forall(int, lambda x: (Implies(2 <= x and x <= n, tri(x) == ((1 + (x // 2)) if x % 2 == 0 else tri(x - 1) + tri(x - 2) + (x + 3) // 2)), [[tri(x)]])))
            Invariant(Forall(int, lambda x: (Implies(2 <= x and x <= n and x % 2 == 0, tri(x) == (1 + (x // 2))), [[tri(x)]])))
            Invariant(Forall(int, lambda x: (Implies(2 <= x and x <= n and x % 2 == 1, tri(x) == (tri(x - 2) + tri(x - 1) + ((x + 3) // 2))), [[tri(x)]])))
            Invariant(result[(d_1_i_) - (2)] == tri(d_1_i_ - 2))
            Invariant(result[(d_1_i_) - (1)] == tri(d_1_i_ - 1))
            Invariant(Forall(int, lambda d_2_j_:
                (Implies(((0) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_)), ((result)[d_2_j_]) == (tri(d_2_j_))), [[tri(d_2_j_)]]))) # , [[(result)[d_2_j_]]]
            Assert(Forall(int, lambda d_2_j_:
                (Implies(((0) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_)), ((result)[d_2_j_]) == (tri(d_2_j_))), [[tri(d_2_j_)]]))) # , [[(result)[d_2_j_]]]
            if ((d_1_i_ % 2)) == (0):
                result[d_1_i_] = (1) + ((d_1_i_ // 2))
                Assert(((result)[d_1_i_]) == (tri(d_1_i_)))
                Assert(Forall(int, lambda d_2_j_:
                    (Implies(((0) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_)), ((result)[d_2_j_]) == (tri(d_2_j_))), [[tri(d_2_j_)]])))
                Assert(Forall(int, lambda d_2_j_:
                    (Implies(((0) <= (d_2_j_)) and ((d_2_j_) <= (d_1_i_)), ((result)[d_2_j_]) == (tri(d_2_j_))), [[tri(d_2_j_)]])))
            else:
                Assert(result[(d_1_i_) - (2)] == tri(d_1_i_ - 2))
                Assert(result[(d_1_i_) - (1)] == tri(d_1_i_ - 1))
                Assert(tri(d_1_i_) == tri(d_1_i_ - 2) + tri(d_1_i_ - 1) + (d_1_i_ + 3) // 2)
                result[d_1_i_] = (((result)[(d_1_i_) - (2)]) + ((result)[(d_1_i_) - (1)])) + ((((d_1_i_) + (3)) // 2))
                Assert(Implies((result)[(d_1_i_) - (2)] == tri(d_1_i_ - 2) and (result)[(d_1_i_) - (1)] == tri(d_1_i_ - 1), result[d_1_i_] == tri(d_1_i_)))
                Assert(((result)[d_1_i_]) == (tri(d_1_i_)))
                Assert(Forall(int, lambda d_2_j_:
                    (Implies(((0) <= (d_2_j_)) and ((d_2_j_) < (d_1_i_)), ((result)[d_2_j_]) == (tri(d_2_j_))), [[tri(d_2_j_)]])))
                Assert(Forall(int, lambda d_2_j_:
                    (Implies(((0) <= (d_2_j_)) and ((d_2_j_) <= (d_1_i_)), ((result)[d_2_j_]) == (tri(d_2_j_))), [[tri(d_2_j_)]])))
            Assert(((result)[d_1_i_]) == (tri(d_1_i_)))
            Assert(Forall(int, lambda d_2_j_:
                (Implies(((0) <= (d_2_j_)) and ((d_2_j_) <= (d_1_i_)), ((result)[d_2_j_]) == (tri(d_2_j_))), [[tri(d_2_j_)]])))
            d_1_i_ = (d_1_i_) + (1)
    return result
