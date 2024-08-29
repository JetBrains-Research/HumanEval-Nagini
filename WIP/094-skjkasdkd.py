from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def skjkasdkd(lst : List[int]) -> int:
    Requires(Acc(list_pred(lst)))
    Requires(Forall(int, lambda d_0_i_: Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(lst))), ((lst)[d_0_i_]) >= (0))))
    Requires(Exists(int, lambda d_0_i_:
        (((0) <= (d_0_i_)) and ((d_0_i_) < (len(lst)))) and (is__prime((lst)[d_0_i_]))))
    Ensures(Acc(list_pred(lst)))
    Ensures((Result()) == (digits__sum(max__seq(filter__primes(lst)))))
    dsum = int(0) # type : int
    d_1_primes_ = list([int(0)] * 0) # type : List[int]
    d_1_primes_ = list([])
    d_2_i_ = int(0) # type : int
    d_2_i_ = 0
    while (d_2_i_) < (len(lst)):
        Invariant(Acc(list_pred(d_1_primes_)))
        Invariant(Acc(list_pred(lst)))
        Invariant(Forall(int, lambda d_0_i_: Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(lst))), ((lst)[d_0_i_]) >= (0))))
        Invariant(Forall(int, lambda d_0_i_: Implies(((0) <= (d_0_i_)) and ((d_0_i_) < (len(d_1_primes_))), ((d_1_primes_)[d_0_i_]) >= (0))))
        Invariant(((0) <= (d_2_i_)) and ((d_2_i_) <= (len(lst))))
        # Invariant((d_1_primes_) == (filter__primes(list((lst)[:d_2_i_:]))))
        if is__prime((lst)[d_2_i_]):
            d_1_primes_ = (d_1_primes_) + [(lst)[d_2_i_]]
        Assert((filter__primes(list((lst)[:(d_2_i_) + (1):]))) == ((filter__primes(list((lst)[:d_2_i_:]))) + ((list([(lst)[d_2_i_]]) if is__prime((lst)[d_2_i_]) else list([])))))
        d_2_i_ = (d_2_i_) + (1)
    Assert((list((lst)[:len(lst):])) == (lst))
    d_3_max__prime_ = int(0) # type : int
    d_3_max__prime_ = (d_1_primes_)[0]
    d_2_i_ = 1
    while (d_2_i_) < (len(d_1_primes_)):
        Invariant(Acc(list_pred(d_1_primes_)))
        Invariant(Acc(list_pred(lst)))
        Invariant(((1) <= (d_2_i_)) and ((d_2_i_) <= (len(d_1_primes_))))
        Invariant(Forall(int, lambda d_4_j_:
            not (((0) <= (d_4_j_)) and ((d_4_j_) < (d_2_i_))) or ((d_3_max__prime_) >= ((d_1_primes_)[d_4_j_]))))
        Invariant((d_3_max__prime_) == (max__seq(list((d_1_primes_)[:d_2_i_:]))))
        d_3_max__prime_ = max(d_3_max__prime_, (d_1_primes_)[d_2_i_])
        Assert((max__seq(list((d_1_primes_)[:(d_2_i_) + (1):]))) == (max(max__seq(list((d_1_primes_)[:d_2_i_:])), (d_1_primes_)[d_2_i_])))
        d_2_i_ = (d_2_i_) + (1)
    Assert((list((d_1_primes_)[:len(d_1_primes_):])) == (d_1_primes_))
    Assert((d_3_max__prime_) == (max__seq(d_1_primes_)))
    dsum = digits__sum(d_3_max__prime_)
    return dsum

@Pure
def digits__sum(x : int) -> int :
    Requires((x) >= (0))
    if x < 10:
        return x % 10
    else:
        return (x % 10) + digits__sum(x // 10)

@Pure
def max__seq(lst : List[int], i : int, j : int) -> int :
    Requires(Acc(list_pred(lst)))
    Requires(((0) <= (i)) and ((i) <= (j)) and ((j) <= (len(lst))))
    if j == i + 1:
        return (lst)[j - 1]
    else:
        return max((lst)[j - 1], max__seq(lst, i, j - 1))

@Pure 
def get_max_prime(list : List[int], i : int, j : int) -> int:
    Requires()

# @staticmethod
# def filter__primes(lst : List[int]) -> List[int] :
#     if (len(lst)) == (0):
#         return list([])
#     elif True:
#         d_7_tail_ = filter__primes(list((lst)[1::])) # type : List[int]
#         return ((list([(lst)[0]]) if is__prime((lst)[0]) else list([]))) + (d_7_tail_)

@Pure
def max(a : int, b : int) -> int :
    if (a) > (b):
        return a
    elif True:
        return b

@Pure
def is__prime(k : int) -> bool :
    Requires((k) >= (0))
    return ((k) != (1)) and (Forall(int, lambda d_8_i_:
        not (((2) <= (d_8_i_)) and ((d_8_i_) < (k))) or (((k % d_8_i_)) != (0))))

