from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *


@Pure
def psum(i : int, j : int, s : List[float]) -> float :
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] == s[d_2_i_])))
    Requires(0 <= i and i <= j and j <= len(s))
    if i == j:
        return 0
    else:
        return (s)[j - 1] + (psum(i, j - 1, s))
    
@Pure
def abs(x : float) -> float:
    Requires(x == x)
    Ensures(Result() >= 0)
    if x < 0:
        return -x
    return x

@Pure
def pmean(s : List[float]) -> float :
    Requires(Acc(list_pred(s)))
    Requires(len(s) > 0)
    Requires(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] == s[d_2_i_])))
    return psum(0, len(s), s) / len(s)

@Pure 
def pderiv(i : int, j : int, s : List[float], m : float) -> float:
    Requires(Acc(list_pred(s)))
    Requires(len(s) > 0)
    Requires(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] - m == s[d_2_i_] - m)))
    Requires(0 <= i and i <= j and j <= len(s))
    Requires(m == m)
    Requires(m == pmean(s))
    if i == j:
        return 0
    else:
        return abs((s)[j - 1] - m) + (pderiv(i, j - 1, s, m))

@Pure 
def pderiv_mean( s : List[float], m : float) -> float:
    Requires(Acc(list_pred(s)))
    Requires(len(s) > 0)
    Requires(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] == s[d_2_i_])))
    Requires(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] - m == s[d_2_i_] - m)))
    Requires(m == m)
    Requires(m == pmean(s))
    Requires(len(s) > 0)
    return pderiv(0, len(s), s, m) / len(s)

def mean_absolute_derivation(s : List[float]) -> float:
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] == s[d_2_i_])))
    Requires(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] - pmean(s) == s[d_2_i_] - pmean(s))))
    Requires(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), psum(0, d_2_i_, s) + s[d_2_i_] == psum(0, d_2_i_, s) + s[d_2_i_])))
    Requires(len(s) > 0)
    Ensures(Acc(list_pred(s)))
    Ensures(len(s) > 0)
    # Ensures(Result() == pderiv_mean(s, pmean(s)))
    # Ensures(Result() >= 0)

    sum = float("0") # type : float
    i = 0 # type : int
    while i < len(s):
        Invariant(Acc(list_pred(s)))
        Invariant(len(s) > 0)
        Invariant(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] == s[d_2_i_])))
        Invariant(0 <= i and i <= len(s))
        Invariant(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), psum(0, d_2_i_, s) + s[d_2_i_] == psum(0, d_2_i_, s) + s[d_2_i_])))
        Invariant(Forall(int, lambda d_2_i_: (not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(s)))) or ((psum(0, d_2_i_ + 1, s)) == (psum(0, d_2_i_, s) + s[d_2_i_])), [[psum(0, d_2_i_ + 1, s)]])))
        Invariant(Forall(int, lambda d_2_i_: (Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] - pmean(s) == s[d_2_i_] - pmean(s)), [[s[d_2_i_]]])))
        Invariant(sum == psum(0, i, s))
        Assert((psum(0, (i) + (1), s)) == ((psum(0, i, s) + (s)[i])))
        sum += s[i]
        i += 1

    # m = sum / len(s) # type : float
    # Assert(m == m)
    Assert(sum == sum)
    Assert(len(s) > 0)
    Assert(sum == psum(0, len(s), s))
    m = sum / len(s) # type : float
    Assert(m == m)
    Assert(m == pmean(s))
    Assert(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] == s[d_2_i_])))
    # Assert(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] - m == s[d_2_i_] - m)))

    # t = float("0") # type : float
    # i = 0 # type : int
    # while i < len(s):
    #     Invariant(Acc(list_pred(s)))
    #     Invariant(len(s) > 0)
    #     Invariant(0 <= i and i <= len(s))
    #     Invariant(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), s[d_2_i_] == s[d_2_i_])))
    #     Invariant(m == pmean(s))
    #     Invariant(Forall(int, lambda d_2_i_: Implies(0 <= d_2_i_ and d_2_i_ < len(s), psum(0, d_2_i_, s) + s[d_2_i_] == psum(0, d_2_i_, s) + s[d_2_i_])))
    #     Invariant(t == pderiv(0, i, s, m))

    #     Assert(pderiv(0, i + 1, s, m) == pderiv(0, i, s, m) + abs(s[i] - m))
    #     t += abs(s[i] - m)
    #     i += 1

    # Assert(t == t)
    # Assert(len(s) > 0)
    # Assert(t == pderiv(0, len(s), s, m))    
    # res  = t / len(s) 
    # Assert(res == res)
    # Assert(res == pderiv_mean(s, m))
        
    return m
    
    

