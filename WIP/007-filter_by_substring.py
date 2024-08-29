from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def checkSubstring(s : List[int], sub : List[int]) -> bool:
    Requires(Acc(list_pred(s),1/2))
    Requires(Acc(list_pred(sub), 1/2))
    Ensures(Acc(list_pred(s),1/2))
    Ensures(Acc(list_pred(sub), 1/2))
    result = False # type : bool
    result = False
    if (len(sub)) == (0):
        result = True
    elif (len(s)) >= (len(sub)):
        d_0_i_ = int(0) # type : int
        d_0_i_ = 0
        while (d_0_i_) <= ((len(s)) - (len(sub))):
            Invariant(Acc(list_pred(s), 1/2))
            Invariant(Acc(list_pred(sub), 1/2))
            Invariant(len(s) - len(sub) >= 0)
            Invariant(((0) <= (d_0_i_)) and ((d_0_i_) <= 1 + ((len(s)) - (len(sub)))))
            x = 0 
            fl = True
            while x < len(sub):
                Invariant(Acc(list_pred(s), 1/2))
                Invariant(Acc(list_pred(sub), 1/2))
                Invariant(len(s) - len(sub) >= 0)
                Invariant(((0) <= (d_0_i_)) and ((d_0_i_) <= ((len(s)) - (len(sub)))))
                Invariant(x >= 0 and x <= len(sub))
                if sub[x] != s[d_0_i_ + x]:
                    fl = False
                    break
                x = x + 1
            if fl:
                result = True
            d_0_i_ = (d_0_i_) + (1)
    return result

@Pure 
def EqArrays(a : List[int], x : List[int]) -> bool :
    Requires(Acc(list_pred(a)))
    Requires(Acc(list_pred(x)))
    return len(a) == len(x) and Forall(int, lambda d_0_i_: Implies(0 <= d_0_i_ and d_0_i_ < len(a), (a)[d_0_i_] == x[d_0_i_]))

@Pure 
def InArray(a : List[List[int]], x : List[int]) -> bool :
    Requires(Acc(list_pred(a)))
    Requires(Acc(list_pred(x)))
    Requires(Forall(a, lambda d_0_s_: Acc(list_pred(d_0_s_))))
    return Exists(int, lambda d_0_s_:
        (Implies(((0) <= (d_0_s_)) and ((d_0_s_) < (len((a)))), 
            EqArrays(a[d_0_s_], x))))

# @Pure 
# def AccBiDim(a : List[List[int]]) -> bool :
#     Requires(Acc(list_pred(a)))
#     return Forall(a, lambda d_0_s_: Acc(list_pred(d_0_s_)))

def filter__by__substring(strings : List[List[int]], substring : List[int]) -> List[List[int]]:
    Requires(Acc(list_pred(strings)))
    Requires(Forall(strings, lambda d_0_s_: Acc(list_pred(d_0_s_))))
    Requires(Acc(list_pred(substring)))
    Ensures(Acc(list_pred(strings)))
    Ensures(Forall(strings, lambda d_0_s_: Acc(list_pred(d_0_s_))))
    Ensures(Acc(list_pred(Result())))
    # Ensures(AccBiDim(Result()))
    Ensures((len(Result())) <= (len(strings)))
    # Ensures(Forall(List[int], lambda d_3_s_: Implies(Exists(int, lambda x : Implies(x >= 0 and x < len(Result()), Result()[x] == d_3_s_)), Acc(list_pred(d_3_s_)))))
    # Ensures(Forall(int, lambda d_3_i_:
    #     (Implies(0 <= d_3_i_ and d_3_i_ < len(Result()), Acc(list_pred(Result()[d_3_i_])) and InArray(strings, Result()[d_3_i_])))))
    # Ensures(Forall(List[int], lambda d_1_s_:
    #     not ((d_1_s_) in (Result())) or ((d_1_s_) in (strings))))
    res : List[List[int]] = []
    d_2_i_ = int(0) # type : int
    d_2_i_ = 0
    while (d_2_i_) < (len(strings)):
        Invariant(Acc(list_pred(res)))
        Invariant(Acc(list_pred(strings)))
        Invariant(Acc(list_pred(substring)))
        Invariant(Forall(strings, lambda d_0_s_: Acc(list_pred(d_0_s_))))
        Invariant(Forall(res, lambda d_3_s_: Acc(list_pred(d_3_s_))))
        Invariant(((0) <= (d_2_i_)) and ((d_2_i_) <= (len(strings))))
        Invariant((len(res)) <= (d_2_i_))
        Invariant(Forall(int, lambda d_3_i_:
            (Implies(0 <= d_3_i_ and d_3_i_ < len(res), InArray(strings, res[d_3_i_])), [[InArray(strings, res[d_3_i_])]])))
        # Invariant(Forall(List[int], lambda d_3_s_:
        #     not ((d_3_s_) in (res)) or ((d_3_s_) in (strings))))
        d_4_check_ = False # type : bool
        d_4_check_ = checkSubstring((strings)[d_2_i_], substring)
        if d_4_check_:
            cpy = list((strings)[d_2_i_])
            res = (res) + [cpy]
        d_2_i_ = (d_2_i_) + (1)
    return res
