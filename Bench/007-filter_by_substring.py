from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def checkSubstring(s : List[int], sub : List[int]) -> bool:
    # pre-conditions-start
    Requires(Acc(list_pred(s), 1/2))
    Requires(Acc(list_pred(sub), 1/2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s), 1/2))
    Ensures(Acc(list_pred(sub), 1/2))
    # post-conditions-end

    # impl-start
    result = False # type : bool
    result = False
    if (len(sub)) == (0):
        result = True
    elif (len(s)) >= (len(sub)):
        d_0_i_ = int(0) # type : int
        d_0_i_ = 0
        while (d_0_i_) <= ((len(s)) - (len(sub))):
            # invariants-start
            Invariant(Acc(list_pred(s), 1/2))
            Invariant(Acc(list_pred(sub), 1/2))
            Invariant(len(s) - len(sub) >= 0)
            Invariant(((0) <= (d_0_i_)) and ((d_0_i_) <= 1 + ((len(s)) - (len(sub)))))
            # invariants-end
            x = 0 
            fl = True
            while x < len(sub):
                # invariants-start
                Invariant(Acc(list_pred(s), 1/2))
                Invariant(Acc(list_pred(sub), 1/2))
                Invariant(len(s) - len(sub) >= 0)
                Invariant(((0) <= (d_0_i_)) and ((d_0_i_) <= ((len(s)) - (len(sub)))))
                Invariant(x >= 0 and x <= len(sub))
                # invariants-end
                if sub[x] != s[d_0_i_ + x]:
                    fl = False
                    break
                x = x + 1
            if fl:
                result = True
            d_0_i_ = (d_0_i_) + (1)
    return result
    # impl-end

@Pure 
def EqArrays(a : List[int], x : List[int]) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    Requires(Acc(list_pred(x)))
    # pre-conditions-end

    # impl-start
    return len(a) == len(x) and Forall(int, lambda d_0_i_: Implies(0 <= d_0_i_ and d_0_i_ < len(a), (a)[d_0_i_] == x[d_0_i_]))
    # impl-end

@Pure 
def InArray(a : List[List[int]], x : List[int]) -> bool :
    # pre-conditions-start
    Requires(Acc(list_pred(a)))
    Requires(Acc(list_pred(x)))
    Requires(Forall(a, lambda d_0_s_: Acc(list_pred(d_0_s_))))
    # pre-conditions-end

    # impl-start
    return Exists(int, lambda d_0_s_:
        (Implies(((0) <= (d_0_s_)) and ((d_0_s_) < (len((a)))), 
            EqArrays(a[d_0_s_], x))))
    # impl-end


def filter__by__substring(strings : List[List[int]], substring : List[int]) -> List[List[int]]:
    # pre-conditions-start
    Requires(Acc(list_pred(strings)))
    Requires(Forall(strings, lambda d_0_s_: Acc(list_pred(d_0_s_))))
    Requires(Acc(list_pred(substring)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(strings)))
    Ensures(Forall(strings, lambda d_0_s_: Acc(list_pred(d_0_s_))))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(ResultT(List[List[int]]), lambda d_0_s_: Acc(list_pred(d_0_s_))))
    Ensures((len(Result())) <= (len(strings)))
    Ensures(Forall(int, lambda d_3_i_:
        (Implies(0 <= d_3_i_ and d_3_i_ < len(Result()), InArray(strings, Result()[d_3_i_])))))
    # post-conditions-end

    # impl-start
    res : List[List[int]] = []
    d_2_i_ = int(0) # type : int
    d_2_i_ = 0
    while (d_2_i_) < (len(strings)):
        # invariants-start
        Invariant(Acc(list_pred(res)))
        Invariant(Acc(list_pred(strings)))
        Invariant(Acc(list_pred(substring)))
        Invariant(Forall(strings, lambda d_0_s_: Acc(list_pred(d_0_s_))))
        Invariant(Forall(res, lambda d_3_s_: Acc(list_pred(d_3_s_))))
        Invariant(((0) <= (d_2_i_)) and ((d_2_i_) <= (len(strings))))
        Invariant((len(res)) <= (d_2_i_))
        Invariant(Forall(int, lambda d_3_i_:
            (Implies(0 <= d_3_i_ and d_3_i_ < len(res), InArray(strings, res[d_3_i_])), [[InArray(strings, res[d_3_i_])]])))
        # invariants-end
        d_4_check_ = False # type : bool
        d_4_check_ = checkSubstring((strings)[d_2_i_], substring)
        if d_4_check_:
            cpy = list((strings)[d_2_i_])
            res = (res) + [cpy]
        d_2_i_ = (d_2_i_) + (1)
    return res
    # impl-end
