from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

# def parse__paren__group(s : List[int]) -> int:
#     Requires(Forall(int, lambda d_0_i_:
#         not (((d_0_i_) >= (0)) and ((d_0_i_) < (len(s)))) or ((((s)[d_0_i_]) == (1)) or (((s)[d_0_i_]) == (2)))))
#     Ensures((Result()) >= (0))
#     max__depth = int(0) # type : int
#     d_1_depth_ = int(0) # type : int
#     d_1_depth_ = 0
#     max__depth = 0
#     d_2_i_ = int(0) # type : int
#     d_2_i_ = 0
#     while (d_2_i_) < (len(s)):
#         d_3_c_ = (s)[d_2_i_] # type : int
#         if (d_3_c_) == (1):
#             d_1_depth_ = (d_1_depth_) + (1)
#             if (d_1_depth_) > (max__depth):
#                 max__depth = d_1_depth_
#         else:
#             d_1_depth_ = (d_1_depth_) - (1)
#         d_2_i_ = (d_2_i_) + (1)
#     return max__depth

def split(s : List[int]) -> List[List[int]]:
    # Requires(Forall(int, lambda d_4_i_:
    #     not (((d_4_i_) >= (0)) and ((d_4_i_) < (len(s)))) or (((((s)[d_4_i_]) == (1)) or (((s)[d_4_i_]) == (2))) or (((s)[d_4_i_]) == (3)))))
    # Ensures(Acc(list_pred(Result())))
    # Ensures(Forall(int, lambda d_5_i_: Implies(d_5_i_ >= 0 and d_5_i_ < len(Result()), Acc(list_pred(Result()[d_5_i_])))))
    # Ensures(Forall(int, lambda d_10_j_:
    #     not (d_10_j_ >= 0 and d_10_j_ < len(Result())) or ((Forall(int, lambda d_11_j_:
    #         not (((d_11_j_) >= (0)) and ((d_11_j_) < (len(Result()[d_10_j_])))) or ((((Result()[d_10_j_])[d_11_j_]) == (1)) or (((Result()[d_10_j_])[d_11_j_]) == (2))))) and ((len(Result()[d_10_j_])) > (0)))))
    res = list([([int(0)] * 0)] * 0) # type : List[List[int]]
    d_7_current__string_ = list([int(0)] * 0) # type : List[int]
    d_8_i_ = int(0) # type : int
    d_8_i_ = 0
    while (d_8_i_) < (len(s)):
        # Invariant(Acc(list_pred(res)))
        # Invariant(Forall(int, lambda d_9_j_: Implies(d_9_j_ >= 0 and d_9_j_ < len(res), Acc(list_pred(res[d_9_j_])))))
        # Invariant(((d_8_i_) >= (0)) and ((d_8_i_) <= (len(s))))
        # Invariant(Forall(int, lambda d_9_j_:
        #     not (((d_9_j_) >= (0)) and ((d_9_j_) < (len(d_7_current__string_)))) or ((((d_7_current__string_)[d_9_j_]) == (1)) or (((d_7_current__string_)[d_9_j_]) == (2)))))
        # Invariant(Forall(int, lambda d_10_j_:
        #     not (d_10_j_ >= 0 and d_10_j_ < len(res)) or ((Forall(int, lambda d_11_j_:
        #         not (((d_11_j_) >= (0)) and ((d_11_j_) < (len(res[d_10_j_])))) or ((((res[d_10_j_])[d_11_j_]) == (1)) or (((res[d_10_j_])[d_11_j_]) == (2))))) and ((len(res[d_10_j_])) > (0)))))
        if ((s)[d_8_i_]) == (3):
            if (d_7_current__string_) != []:
                res = (res) + [d_7_current__string_]
                d_7_current__string_ = []
        else:
            d_7_current__string_ = (d_7_current__string_) + [(s)[d_8_i_]]
        d_8_i_ = (d_8_i_) + (1)
    if (d_7_current__string_) != []:
        res = (res) + [d_7_current__string_]
        d_7_current__string_ =  []
    return res

# def parse__nested__parens(paren__string : List[int]) -> List[int]:
#     Requires(Forall(int, lambda d_12_i_:
#         not (((d_12_i_) >= (0)) and ((d_12_i_) < (len(paren__string)))) or (((((paren__string)[d_12_i_]) == (1)) or (((paren__string)[d_12_i_]) == (2))) or (((paren__string)[d_12_i_]) == (3)))))
#     Ensures(Acc(list_pred(Result())))
#     Ensures(Forall(int, lambda d_13_x_:
#         Implies(d_13_x_ >= 0 and d_13_x_ < len(Result()), Result()[d_13_x_] >= 0)))
#     res = list([int(0)] * 0) # type : List[int]
#     d_14_strings_ = split(paren__string) # type : List[List[int]]
#     d_15_i_ = int(0) # type : int
#     while (d_15_i_) < (len(d_14_strings_)):
#         Invariant(Acc(list_pred(d_14_strings_)))
#         Invariant(Acc(list_pred(res)))
#         Invariant(Forall(int, lambda d_5_i_: Implies(d_5_i_ >= 0 and d_5_i_ < len(d_14_strings_), Acc(list_pred(d_14_strings_[d_5_i_])))))
#         Invariant(((d_15_i_) >= (0)) and ((d_15_i_) <= (len(d_14_strings_))))
#         Invariant(Forall(int, lambda d_13_x_:
#             Implies(d_13_x_ >= 0 and d_13_x_ < len(res), res[d_13_x_] >= 0)))
#         d_17_cur_ = parse__paren__group((d_14_strings_)[d_15_i_]) # type : int
#         res = (res) + [d_17_cur_]
#         d_15_i_ = (d_15_i_) + (1)
#     return res