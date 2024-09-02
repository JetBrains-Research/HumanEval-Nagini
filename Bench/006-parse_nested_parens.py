from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def parseparengroup(s : List[int]) -> int:
    Requires(Acc(list_pred(s), 1/2))
    Requires(contains12(s))
    Requires(get_len(s))
    Ensures(Acc(list_pred(s), 1/2))
    Ensures(contains12(s))
    Ensures(get_len(s))
    Ensures((Result()) >= (0))
    max__depth = int(0) # type : int
    d_1_depth_ = int(0) # type : int
    d_1_depth_ = 0
    max__depth = 0
    d_2_i_ = int(0) # type : int
    d_2_i_ = 0
    while (d_2_i_) < (len(s)):
        Invariant(Acc(list_pred(s), 1/2))
        Invariant(((d_2_i_) >= (0)) and ((d_2_i_) <= (len(s))))
        Invariant(max__depth >= 0)
        Invariant(contains12(s))
        Invariant(get_len(s))
        d_3_c_ = (s)[d_2_i_] # type : int
        if (d_3_c_) == (1):
            d_1_depth_ = (d_1_depth_) + (1)
            if (d_1_depth_) > (max__depth):
                max__depth = d_1_depth_
        else:
            d_1_depth_ = (d_1_depth_) - (1)
        d_2_i_ = (d_2_i_) + (1)
    return max__depth

@Pure 
def get_len(s : List[int]) -> bool:
    Requires(Acc(list_pred(s), 1/2))
    return len(s) > 0

@Pure 
def contains12(s : List[int]) -> bool:
    Requires(Acc(list_pred(s), 1/2))
    return Forall(int, lambda d_0_i_: 
        Implies(d_0_i_ >= 0 and d_0_i_ < len(s), s[d_0_i_] == 1 or s[d_0_i_] == 2))

def split(s : List[int]) -> List[List[int]]:
    Requires(Acc(list_pred(s)))
    Requires(Forall(int, lambda d_4_i_:
        not (((d_4_i_) >= (0)) and ((d_4_i_) < (len(s)))) or (((((s)[d_4_i_]) == (1)) or (((s)[d_4_i_]) == (2))) or (((s)[d_4_i_]) == (3)))))
    Ensures(Acc(list_pred(ResultT(List[List[int]]))))
    Ensures(Forall(ResultT(List[List[int]]), lambda x: Acc(list_pred(x), 1/2)))
    Ensures(Forall(int, lambda d_10_j_:
        Implies(d_10_j_ >= 0 and d_10_j_ < len(ResultT(List[List[int]])), (get_len(ResultT(List[List[int]])[d_10_j_])))))
    Ensures(Forall(int, lambda d_10_j_:
        (Implies(d_10_j_ >= 0 and d_10_j_ < len(Result()), 
            contains12(Result()[d_10_j_])), [[contains12(Result()[d_10_j_])]])))
    res : List[List[int]] = [] # type : List[List[int]]
    d_7_current__string_ : List[int] = [] # type : List[int]
    d_8_i_ = int(0) # type : int
    d_8_i_ = 0
    while (d_8_i_) < (len(s)):
        Invariant(Acc(list_pred(res)))
        Invariant(Forall(res, lambda x: Acc(list_pred(x), 1/2)))
        Invariant(Acc(list_pred(d_7_current__string_)))
        Invariant(Acc(list_pred(s)))
        Invariant(((d_8_i_) >= (0)) and ((d_8_i_) <= (len(s))))
        Invariant(Forall(int, lambda d_4_i_:
            (not (((d_4_i_) >= (0)) and ((d_4_i_) < (len(s)))) or (((((s)[d_4_i_]) == (1)) or 
             (((s)[d_4_i_]) == (2))) or (((s)[d_4_i_]) == (3))), [[]])))
        Invariant(Forall(int, lambda d_4_i_:
            (not (((d_4_i_) >= (0)) and ((d_4_i_) < (len(d_7_current__string_)))) or 
             (((((d_7_current__string_)[d_4_i_]) == (1)) or (((d_7_current__string_)[d_4_i_]) == (2)))), [[]])))
        Invariant(Forall(int, lambda d_10_j_:
            (Implies(d_10_j_ >= 0 and d_10_j_ < len(res), ((get_len(res[d_10_j_])))), [[]])))
        Invariant(Forall(int, lambda d_10_j_:
            (Implies(d_10_j_ >= 0 and d_10_j_ < len(res), 
                contains12(res[d_10_j_])), [[contains12(res[d_10_j_])]])))
        if ((s)[d_8_i_]) == (3):
            if len(d_7_current__string_) > 0:
                d_7_copy = list(d_7_current__string_)
                res = (res) + [d_7_copy]
                d_7_current__string_ = []
        else:
            d_7_current__string_ = (d_7_current__string_) + [(s)[d_8_i_]]
        d_8_i_ = (d_8_i_) + (1)
    if len(d_7_current__string_) > 0:
        d_7_copy = list(d_7_current__string_)
        Assert(get_len(d_7_copy))
        res = (res) + [d_7_copy]
        # Assert(Forall(int, lambda d_10_j_:
        #     (Implies(d_10_j_ >= 0 and d_10_j_ < len(res), ((get_len(res[d_10_j_])))), [[]])))
        d_7_current__string_ =  []
    return res

def parse__nested__parens(paren__string : List[int]) -> List[int]:
    Requires(Acc(list_pred(paren__string)))
    Requires(Forall(int, lambda d_12_i_:
        not (((d_12_i_) >= (0)) and ((d_12_i_) < (len(paren__string)))) or (((((paren__string)[d_12_i_]) == (3)) or (((paren__string)[d_12_i_]) == (1))) or (((paren__string)[d_12_i_]) == (2)))))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(ResultT(List[int]), lambda d_13_x_: ((d_13_x_) >= (0))))
    res : List[int] = []
    d_14_strings_ : List[List[int]] = split(paren__string)
    d_15_i_ = int(0) # type : int
    while (d_15_i_) < (len(d_14_strings_)):
        Invariant(Acc(list_pred(d_14_strings_)))
        Invariant(Acc(list_pred(res)))
        Invariant(Forall(d_14_strings_, lambda x: Acc(list_pred(x), 1/2)))
        Invariant(0 <= d_15_i_ and d_15_i_ <= len(d_14_strings_))
        Invariant(Forall(res, lambda d_16_x_: ((d_16_x_) >= (0))))
        Invariant(Forall(int, lambda d_10_j_:
            Implies(d_10_j_ >= 0 and d_10_j_ < len(d_14_strings_), (get_len(d_14_strings_[d_10_j_])))))
        Invariant(Forall(int, lambda d_10_j_:
            (Implies(d_10_j_ >= 0 and d_10_j_ < len(d_14_strings_), 
                contains12(d_14_strings_[d_10_j_])), [[contains12(d_14_strings_[d_10_j_])]])))
        d_17_cur_ = int(0) # type : int
        d_17_cur_ = parseparengroup((d_14_strings_)[d_15_i_])
        res = (res) + [d_17_cur_]
        d_15_i_ = (d_15_i_) + (1)
    return res