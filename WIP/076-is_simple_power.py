from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def power(x : int, y : int) -> int :
    Requires(x >= 1)
    Requires(y >= 0)
    Ensures(Result() >= 1)
    Ensures(Implies(x == 1, Result() == 1))
    if y == 0:
        return 1
    else:
        return x * power(x, y - 1)

def is__simple__power(x : int, n : int) -> bool:
    Requires((x) > (0))
    Requires(n >= 0)
    # Ensures((Result()) == (Exists(int, lambda d_1_y_:
    #     n >= d_1_y_ and d_1_y_ >= 0 and (n) == (power(x, d_1_y_)))))
    if (x) == (1):
        Assert(Forall(int, lambda d_2_y_: (Implies(d_2_y_ >= 0, (power(x, d_2_y_)) == (1)), [[power(x, d_2_y_)]])))
        Assert(not ((n) == (1)) or ((n) == (power(x, 1))))
        return n == 1
    d_3_acc_ = int(0) # type : int
    d_3_acc_ = 1
    d_4_i_ = int(0) # type : int
    d_4_i_ = 0
    while (d_3_acc_) < (n):
        Invariant(x > 1)
        Invariant(n >= 0)
        Invariant(d_4_i_ >= 0)
        Invariant(d_3_acc_ >= 1)
        Invariant(Forall(int, lambda y: (Implies(y >= 0, power(x, y + 1) == x * power(x, y)), [[power(x, y + 1)]])))
        Invariant(Forall(int, lambda y: (Implies(y >= 0, power(x, y + 1) > power(x, y)), [[power(x, y + 1)]])))
        Invariant(Forall(int, lambda y: (Implies(d_4_i_ > y and y >= 0, power(x, y) < n), [[power(x, y) < n]])))
        Invariant(d_4_i_ <= d_3_acc_)
        Invariant(d_4_i_ <= n)
        Invariant((d_3_acc_) == (power(x, d_4_i_)))
        Invariant(Forall(int, lambda y: (Implies(d_4_i_ > y and y >= 0 and power(x, y) < n, power(x, y) != n))))
        Invariant(Forall(int, lambda y: (Implies(d_4_i_ > y and y >= 0, power(x, y) < n))))
        Invariant(Forall(int, lambda y: (Implies(d_4_i_ > y and y >= 0, power(x, y) != n))))
        d_3_acc_ = (x) * (d_3_acc_)
        d_4_i_ = (d_4_i_) + (1)
    if (d_3_acc_) == (n):
        Assert((Exists(int, lambda d_1_y_:
            n >= d_1_y_ and d_1_y_ >= 0 and (n) == (power(x, d_1_y_)))))
        return True
    else:
        Assert(power(x, d_4_i_) > n)
        Assert(Forall(int, lambda y: (Implies(d_4_i_ > y and y >= 0, power(x, y) < n))))
        # Assert(Forall(int, lambda d_6_j_:
        #     (Implies(n >= d_6_j_ and (d_6_j_) >= (d_4_i_), (power(x, d_6_j_)) >= power(x, d_4_i_)), [[(power(x, d_6_j_))]])))
        # Assert(Forall(int, lambda y: (Implies(y >= 0 and y < d_4_i_, power(x, y) != n), [[power(x, y) != n]])))
        # Assert(Forall(int, lambda d_6_j_:
        #     Implies(n >= d_6_j_ and (d_6_j_) >= (d_4_i_), (power(x, d_6_j_)) > (n))))
        return False
