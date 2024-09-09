from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def prod(s : List[int], i : int, j : int) -> int :
    Requires(Acc(list_pred(s), 1/2))
    Requires(i >= 0 and i <= len(s))
    Requires(j >= 0 and j <= len(s))
    Requires(i <= j)
    if i == j:
        return 1
    else:
        return s[j - 1] * prod(s, i, j - 1)

def try_divide(n : int, taken : int, temp : int, pre : int, d_1_cur_ : int, d_2_i_ : int, factors : List[int]) -> Tuple[int, int]:
    Requires(d_1_cur_ >= 1 and d_1_cur_ <= n)
    Requires(d_2_i_ >= 2)
    Requires(temp * d_1_cur_ == pre)
    Requires(Acc(list_pred(factors)))
    Requires(prod(factors, 0, len(factors)) == taken)
    Requires(Forall(int, lambda x : 
        (Implies(x >= 0 and x < len(factors), prod(factors, 0, x + 1) == factors[x] * prod(factors, 0, x)))))
    # Ensures(Acc(list_pred(factors)))
    # Ensures(Acc(list_pred(Old(factors))))
    Ensures(Result()[0] >= 1 and Result()[0] <= n)
    Ensures(d_2_i_ >= 2)
    Ensures(Result()[1] * Result()[0] == pre)
    while ((d_1_cur_ % d_2_i_)) == (0):
        Invariant(Acc(list_pred(factors)))
        Invariant(d_1_cur_ >= 1 and d_1_cur_ <= n)
        Invariant(d_2_i_ >= 2)
        Invariant(temp * d_1_cur_ == pre)
        Invariant(Forall(int, lambda x : 
            (Implies(x >= 0 and x < len(Old(factors)), factors[x] == Old(factors)[x]), [[factors[x]]])))
        # Invariant(Forall(int, lambda x : 
        #     (Implies(x >= 0 and x < len(factors), prod(factors, 0, x + 1) == factors[x] * prod(factors, 0, x)), [[prod(factors, 0, x + 1)]])))
        # Invariant(prod(Old(factors), 0, len(Old(factors))) == taken)
        factors = (factors) + [d_2_i_]
        Assert(prod(factors, 0, len(factors)) == factors[len(factors) - 1] * prod(factors, 0, len(factors) - 1))
        d_1_cur_ = (d_1_cur_ // d_2_i_)
        temp = (temp) * (d_2_i_)
    return (d_1_cur_, temp)

# def factorize(n : int) -> List[int]:
#     Requires((n) > (0))
#     Ensures(Acc(list_pred(Result())))
#     # Ensures((prod(Result(), 0, len(Result()))) == (n))
#     factors : List[int] = []
#     d_1_cur_ = n
#     d_2_i_ = 2
#     taken = 1
#     while ((d_2_i_) * (d_2_i_)) <= (d_1_cur_):
#         Invariant(Acc(list_pred(factors)))
#         Invariant(d_2_i_ >= 2)
#         Invariant(d_1_cur_ >= 1 and d_1_cur_ <= n)
#         Invariant(taken * d_1_cur_ == n)
#         # Invariant(prod(factors, 0, len(factors)) == taken)
#         # Invariant(prod(factors, 0, len(factors)) * d_1_cur_ == n)
#         # Invariant((prod(factors)) == (d_3_taken_))
#         # Invariant(((d_3_taken_) * (d_1_cur_)) == (n))
#         temp = 1
#         (d_1_cur_, temp) = try_divide(n, temp, n, d_1_cur_, d_2_i_, factors)
#         # while ((d_1_cur_ % d_2_i_)) == (0):
#         #     Invariant(Acc(list_pred(factors)))
#         #     Invariant(d_1_cur_ >= 1 and d_1_cur_ <= n)
#         #     Invariant(d_2_i_ >= 2)
#         #     Invariant(temp * d_1_cur_ == pre)
#         #     Invariant(prev == Old(prev))
#         #     # Invariant(Forall(int, lambda x : Implies(x >= 0 and x < prev, prev_cur[x] == factors[x])))
#         #     # Invariant(prod(factors, 0, len(factors)) == taken * temp)
#         #     # Invariant(prod(factors, 0, len(factors)) * d_1_cur_ == n)
#         #     # Invariant(((d_4_temp_) * (d_1_cur_)) == (d_5_pre_))
#         #     # Invariant((prod(factors)) == ((d_3_taken_) * (d_4_temp_)))
#         #     # Assume(prod(factors, 0, prev) == taken)
#         #     factors = (factors) + [d_2_i_]
#         #     # Assert(prod(factors, 0, prev) == taken)
#         #     d_1_cur_ = (d_1_cur_ // d_2_i_)
#         #     temp = (temp) * (d_2_i_)
#         #     # Assert(((2) <= (d_2_i_)) and (((2) * (d_1_cur_)) <= ((d_2_i_) * (d_1_cur_))))
#         d_2_i_ = (d_2_i_) + (1)
#         taken = (taken) * (temp)
#     if (d_1_cur_) > (1):
#         factors = (factors) + [d_1_cur_]
#     # Assert((d_3_taken_) == (n))
#     return factors