from typing import List
from nagini_contracts.contracts import *

def comparison(a : List[int], b : List[int], i : int) -> bool :
    Requires(Acc(list_pred(a), 1/2))
    Requires(Acc(list_pred(b), 1/2))
    Requires(i >= 0 and i <= len(a))
    Requires(i >= 0 and i <= len(b))
    Ensures(Acc(list_pred(a), 1/2))
    Ensures(Acc(list_pred(b), 1/2))
    if i < len(a) and i < len(b):
        if a[i] < b[i]:
            return True
        elif a[i] > b[i]:
            return False
        else:
            return comparison(a, b, i + 1)
    elif len(a) < len(b):
        return True
    else:
        return False

# def sort__strings(lst : List[List[int]]) -> List[List[int]]:
#     Requires(Acc(list_pred(lst)))
#     Requires(Forall(lst, lambda x: Acc(list_pred(x))))
#     Ensures(Acc(list_pred(lst)))
#     Ensures(Forall(lst, lambda x: Acc(list_pred(x))))
#     Ensures(Acc(list_pred(ResultT(List[List[int]]))))
#     Ensures(Forall(ResultT(List[List[int]]), lambda x: Acc(list_pred(x))))
#     Ensures((len(Result())) == (len(lst)))
#     sorted : List[List[int]] = [[int(0)]] * len(lst)
#     Assert(Acc(list_pred(sorted)))
#     Assert(Forall(sorted, lambda x: Acc(list_pred(x))))
#     d_0_i_ = int(0) # type : int
#     while d_0_i_ < len(lst):
#         Invariant(Acc(list_pred(sorted)))
#         Invariant(Acc(list_pred(lst)))
#         Invariant(Forall(lst, lambda x: Acc(list_pred(x))))
#         Invariant(Forall(sorted, lambda x: Acc(list_pred(x))))
#         Invariant(((0) <= (d_0_i_)) and ((d_0_i_) <= (len(lst))))
#         Invariant((len(sorted)) == (len(lst)))
#         sorted[d_0_i_] = list(lst[d_0_i_])
#     d_0_i_ = 0
#     while (d_0_i_) < (len(lst)):
#         Invariant(Acc(list_pred(sorted)))
#         Invariant(Acc(list_pred(lst)))
#         Invariant(Forall(lst, lambda x: Acc(list_pred(x))))
#         Invariant(Forall(sorted, lambda x: Acc(list_pred(x))))
#         Invariant(((0) <= (d_0_i_)) and ((d_0_i_) <= (len(lst))))
#         Invariant((len(sorted)) == (len(lst)))
#         d_1_j_ = int(0) # type : int
#         d_1_j_ = (d_0_i_) + (1)
#         d_2_min_ = int(0) # type : int
#         d_2_min_ = d_0_i_
#         while (d_1_j_) < (len(lst)):
#             Invariant(Acc(list_pred(sorted)))
#             Invariant(Acc(list_pred(lst)))
#             Invariant(Forall(lst, lambda x: Acc(list_pred(x))))
#             Invariant(Forall(sorted, lambda x: Acc(list_pred(x))))
#             Invariant((len(sorted)) == (len(lst)))
#             Invariant(((0) <= (d_0_i_)) and ((d_0_i_) < (len(lst))))
#             Invariant((((0) <= (d_0_i_)) and ((d_0_i_) <= (d_1_j_))) and ((d_1_j_) <= (len(lst))))
#             Invariant(((0) <= (d_2_min_)) and ((d_2_min_) < (d_1_j_)))
#             if not(comparison((sorted)[d_2_min_], (sorted)[d_1_j_], 0)):
#                 d_2_min_ = d_1_j_
#             d_1_j_ = (d_1_j_) + (1)
#         d_3_temp_ : List[int] = list((sorted)[d_0_i_])
#         sorted[d_0_i_] = list(sorted[d_2_min_])
#         sorted[d_2_min_] = list(d_3_temp_)
#         d_0_i_ = (d_0_i_) + (1)
#     return sorted

def sort__lengths(lst : List[List[int]]) -> List[List[int]]:
    Requires(Acc(list_pred(lst)))
    Requires(Forall(lst, lambda x: Acc(list_pred(x))))
    Requires(Forall(int, lambda d_4_i_:
        not (((0) <= (d_4_i_)) and ((d_4_i_) < (len(lst)))) or (((len((lst)[d_4_i_]) % 2)) == (0))))
    Ensures(Acc(list_pred(lst)))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(lst, lambda x: Acc(list_pred(x))))
    Ensures(Forall(ResultT(List[List[int]]), lambda x: Acc(list_pred(x))))
    # Ensures(Forall(int, lambda d_5_i_:
    #     not (((0) <= (d_5_i_)) and ((d_5_i_) < (len(Result())))) or (((len((Result())[d_5_i_]) % 2)) == (0))))
    Ensures((len(Result())) == (len(lst)))
    # Ensures(Forall(int, lambda d_6_x_:
    #     Forall(int, lambda d_7_y_:
    #         not ((((0) <= (d_6_x_)) and ((d_6_x_) < (d_7_y_))) and ((d_7_y_) < (len(Result())))) or ((len((Result())[d_6_x_])) <= (len((Result())[d_7_y_]))))))
    sorted : List[List[int]] = [[int(0)]] * len(lst)
    Assert(Acc(list_pred(sorted)))
    Assert(Forall(sorted, lambda x: Acc(list_pred(x))))
    d_0_i_ = int(0) # type : int
    while d_0_i_ < len(lst):
        Invariant(Acc(list_pred(sorted)))
        Invariant(Acc(list_pred(lst)))
        Invariant(Forall(lst, lambda x: Acc(list_pred(x))))
        Invariant(Forall(sorted, lambda x: Acc(list_pred(x))))
        Invariant(((0) <= (d_0_i_)) and ((d_0_i_) <= (len(lst))))
        Invariant((len(sorted)) == (len(lst)))
        Invariant(Forall(int, lambda d_4_i_:
            not (((0) <= (d_4_i_)) and ((d_4_i_) < (len(lst)))) or (((len((lst)[d_4_i_]) % 2)) == (0))))
        Invariant(Forall(int, lambda d_4_i_:
            not (((0) <= (d_4_i_)) and ((d_4_i_) < (d_0_i_))) or (((len((sorted)[d_4_i_]) % 2)) == (0))))
        sorted[d_0_i_] = list(lst[d_0_i_])
    d_8_i_ = int(0) # type : int
    d_8_i_ = 0
    while (d_8_i_) < (len(lst)):
        Invariant(Acc(list_pred(sorted)))
        Invariant(Acc(list_pred(lst)))
        Invariant(len(sorted) == len(lst))
        Invariant(Forall(lst, lambda x: Acc(list_pred(x))))
        Invariant(Forall(sorted, lambda x: Acc(list_pred(x))))
        Invariant(Forall(int, lambda d_4_i_:
            (not (((0) <= (d_4_i_)) and ((d_4_i_) < (len(sorted)))) or (((len((sorted)[d_4_i_]) % 2)) == (0)))))
        Invariant(((0) <= (d_8_i_)) and ((d_8_i_) <= (len(lst))))
        Invariant((len(sorted)) == (len(lst)))
        # Invariant(Forall(int, lambda d_9_x_:
        #     not (((0) <= (d_9_x_)) and ((d_9_x_) < (d_8_i_))) or (Forall(int, lambda d_10_y_:
        #         not (((d_8_i_) <= (d_10_y_)) and ((d_10_y_) < (len(sorted)))) or ((len((sorted)[d_9_x_])) <= (len((sorted)[d_10_y_])))))))
        # Invariant(Forall(int, lambda d_11_x_:
        #     Forall(int, lambda d_12_y_:
        #         not ((((0) <= (d_11_x_)) and ((d_11_x_) < (d_12_y_))) and ((d_12_y_) < (d_8_i_))) or ((len((sorted)[d_11_x_])) <= (len((sorted)[d_12_y_]))))))
        d_14_j_ = int(0) # type : int
        d_14_j_ = (d_8_i_) + (1)
        d_15_min_ = int(0) # type : int
        d_15_min_ = d_8_i_
        while (d_14_j_) < (len(lst)):
            Invariant(Acc(list_pred(sorted)))
            Invariant(Acc(list_pred(lst)))
            Invariant(len(sorted) == len(lst))  
            Invariant(Forall(lst, lambda x: Acc(list_pred(x))))
            Invariant(Forall(sorted, lambda x: Acc(list_pred(x))))
            Invariant(Forall(int, lambda d_4_i_:
                (not (((0) <= (d_4_i_)) and ((d_4_i_) < (len(sorted)))) or (((len((sorted)[d_4_i_]) % 2)) == (0)))))
            Invariant((len(sorted)) == (len(lst)))
            Invariant(((0) <= (d_0_i_)) and ((d_8_i_) < (len(lst))))
            Invariant((((0) <= (d_8_i_)) and ((d_8_i_) < (d_14_j_))) and ((d_14_j_) <= (len(lst))))
            Invariant(((d_8_i_) <= (d_15_min_)) and ((d_15_min_) < (d_14_j_)))
            # Invariant(Forall(int, lambda d_16_x_:
            #     not (((d_8_i_) <= (d_16_x_)) and ((d_16_x_) < (d_14_j_))) or ((len((sorted)[d_15_min_])) <= (len((sorted)[d_16_x_])))))
            if (len((sorted)[d_14_j_])) < (len((sorted)[d_15_min_])):
                d_15_min_ = d_14_j_
            d_14_j_ = (d_14_j_) + (1)
        d_17_temp_ : List[int] = list((sorted)[d_8_i_])
        sorted[d_8_i_] = list(sorted[d_15_min_])
        sorted[d_15_min_] = list(d_17_temp_)
        d_8_i_ = (d_8_i_) + (1)
    return sorted

# @staticmethod
# def sorted__list__sum(lst : List[List[int]]) -> List[List[int]]:
#     Requires(Acc(list_pred(lst)))
#     Requires((len(lst)) > (0))
#     Ensures(Acc(list_pred(lst)))
#     Ensures(Acc(list_pred(Result())))
#     Ensures((len(Result())) <= (len(lst)))
#     Ensures(Forall(int, lambda d_18_i_:
#         not (((0) <= (d_18_i_)) and ((d_18_i_) < (len(Result())))) or ((_dafny.euclidian_modulus(len((Result())[d_18_i_]), 2)) == (0))))
#     Ensures(Forall(int, lambda d_19_x_:
#         Forall(int, lambda d_20_y_:
#             not ((((0) <= (d_19_x_)) and ((d_19_x_) < (d_20_y_))) and ((d_20_y_) < (len(Result())))) or ((len((Result())[d_19_x_])) <= (len((Result())[d_20_y_]))))))
#     Ensures((_dafny.MultiSet(Result())).issubset(_dafny.MultiSet(lst)))
#     sorted = list([list(map(_dafny.CodePoint, ""))] * 0) # type : List[List[int]]
#     d_21_init_ = list([list(map(_dafny.CodePoint, ""))] * 0) # type : List[List[int]]
#     out0_ # type : List[List[int]]
#     out0_ = default__.sort__strings(lst)
#     d_21_init_ = out0_
#     sorted = list([])
#     d_22_i_ = int(0) # type : int
#     d_22_i_ = 0
#     while (d_22_i_) < (len(d_21_init_)):
#         Invariant(Acc(list_pred(d_21_init_)))
#         Invariant(Acc(list_pred(sorted)))
#         Invariant(Acc(list_pred(lst)))
#         Invariant((len(d_21_init_)) > (0))
#         Invariant((_dafny.MultiSet(d_21_init_)) == (_dafny.MultiSet(lst)))
#         Invariant(((0) <= (d_22_i_)) and ((d_22_i_) <= (len(d_21_init_))))
#         Invariant((len(sorted)) <= (d_22_i_))
#         Invariant(Forall(int, lambda d_23_i_:
#             not (((0) <= (d_23_i_)) and ((d_23_i_) < (len(sorted)))) or ((_dafny.euclidian_modulus(len((sorted)[d_23_i_]), 2)) == (0))))
#         Invariant((_dafny.MultiSet(sorted)).issubset(_dafny.MultiSet(list((d_21_init_)[0:d_22_i_:]))))
#         #decreases |init| - i
#         if (_dafny.euclidian_modulus(len((d_21_init_)[d_22_i_]), 2)) == (0):
#             sorted = (sorted) + (list([(d_21_init_)[d_22_i_]]))
#             Assert((_dafny.MultiSet(sorted)).issubset(_dafny.MultiSet(list((d_21_init_)[0:(d_22_i_) + (1):]))))
#         elif True:
#             pass
#         d_22_i_ = (d_22_i_) + (1)
#     Assert((_dafny.MultiSet(sorted)).issubset(_dafny.MultiSet(list((d_21_init_)[0:len(d_21_init_):]))))
#     Assert((list((d_21_init_)[0:len(d_21_init_):])) == (d_21_init_))
#     out1_ # type : List[List[int]]
#     out1_ = default__.sort__lengths(sorted)
#     sorted = out1_
#     return sorted
