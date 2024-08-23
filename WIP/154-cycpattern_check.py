from typing import List
from nagini_contracts.contracts import *

@Pure
def IsSubstring(s : List[int], sub : List[int], n : int) -> bool :
    Requires(Acc(list_pred(s)))
    Requires(Acc(list_pred(sub)))
    return ((len(s)) >= (len(sub))) and (Exists(int, lambda d_0_i_:
        (((0) <= (d_0_i_)) and ((d_0_i_) < 1 + ((len(s)) - (len(sub))))) and (
            Forall(int, lambda y: (Implies(y >= 0 and y < len(sub), sub[(n + y) % len(sub)] == s[d_0_i_ + y]), [[sub[(n + y) % len(sub)] == s[d_0_i_ + y]]])))))

# def IsSubstringFunc(s : List[int], sub : List[int], n : int) -> bool :
#     Requires(Acc(list_pred(s)))
#     Requires(Acc(list_pred(sub)))
#     Ensures(Acc(list_pred(s)))
#     Ensures(Acc(list_pred(sub)))
#     Ensures(Implies(Result(), len(s) >= len(sub)))
#     # Ensures(Result() == (((len(s)) >= (len(sub))) and (Exists(int, lambda d_0_i_:
#     #     (((0) <= (d_0_i_)) and ((d_0_i_) < 1 + ((len(s)) - (len(sub))))) and (
#     #         Forall(int, lambda y: (Implies(y >= 0 and y < len(sub), sub[(n + y) % len(sub)] == s[d_0_i_ + y]), [[sub[(n + y) % len(sub)] == s[d_0_i_ + y]]])))))))
    
#     if (len(s) < len(sub)):
#         return False
    
#     i = 0 # type : int
#     while i <= len(s) - len(sub):
#         Invariant(Acc(list_pred(s), 1/2))
#         Invariant(Acc(list_pred(sub), 1/2))
#         Invariant(((0) <= (i)) and ((i) <= 1 + ((len(s)) - (len(sub)))))
#         Invariant(len(s) >= len(sub))
#         # Invariant(Forall(int, lambda d_0_i: 
#         #     (Implies(d_0_i >= 0 and d_0_i < i, 
#         #         Exists(int, lambda y: y >= 0 and y < len(sub) and sub[(n + y) % len(sub)] != s[d_0_i + y])), 
#         #             [[Exists(int, lambda y: y >= 0 and y < len(sub) and sub[(n + y) % len(sub)] != s[d_0_i + y])]])))
        
#         Assume(Forall(int, lambda d_0_i: 
#             (Implies(d_0_i >= 0 and d_0_i < i, 
#                 Exists(int, lambda y: y >= 0 and y < len(sub) and sub[(n + y) % len(sub)] != s[d_0_i + y])), 
#                 [[Exists(int, lambda y: y >= 0 and y < len(sub) and sub[(n + y) % len(sub)] != s[d_0_i + y])]])))
#         j = 0 # type : int
#         fl = True # type : bool
#         Assert(Forall(int, lambda d_0_i: 
#             (Implies(d_0_i >= 0 and d_0_i < i, 
#                 Exists(int, lambda y: y >= 0 and y < len(sub) and sub[(n + y) % len(sub)] != s[d_0_i + y])), 
#                 [[Exists(int, lambda y: y >= 0 and y < len(sub) and sub[(n + y) % len(sub)] != s[d_0_i + y])]])))  
#         while j < len(sub):
#             Invariant(Acc(list_pred(s), 1/2))
#             Invariant(Acc(list_pred(sub), 1/2))
#             Invariant(((0) <= (j)) and ((j) <= (len(sub))))
#             Invariant(((0) <= (i)) and ((i) <= ((len(s)) - (len(sub)))))
#             Invariant(len(s) >= len(sub))
#             Invariant(fl)
#             Invariant(Forall(int, lambda d_0_i: 
#                 (Implies(d_0_i >= 0 and d_0_i < i, 
#                     Exists(int, lambda y: y >= 0 and y < len(sub) and sub[(n + y) % len(sub)] != s[d_0_i + y])), 
#                     [[Exists(int, lambda y: y >= 0 and y < len(sub) and sub[(n + y) % len(sub)] != s[d_0_i + y])]])))  
#             Invariant(Implies(fl, Forall(int, lambda y: (Implies(y >= 0 and y < j, sub[(n + y) % len(sub)] == s[i + y]), [[sub[(n + y) % len(sub)] == s[i + y]]]))))
#             if sub[(n + j) % len(sub)] != s[i + j]:
#                 fl = False
#                 Assert(fl == (j == len(sub)))
#                 break
#             j = j + 1

#         Assert(fl == (j == len(sub)))
#         if j == len(sub):
#             Assert(IsSubstring(s, sub, n))
#             return True
#         Assert(Exists(int, lambda y: y >= 0 and y < len(sub) and sub[(n + y) % len(sub)] != s[i + y]))
#         Assert(Forall(int, lambda d_0_i: 
#             (Implies(d_0_i >= 0 and d_0_i <= i, 
#                 Exists(int, lambda y: y >= 0 and y < len(sub) and sub[(n + y) % len(sub)] != s[d_0_i + y])), 
#                 [[Exists(int, lambda y: y >= 0 and y < len(sub) and sub[(n + y) % len(sub)] != s[d_0_i + y])]])))
#         i = i + 1
#     return False

# def CycpatternCheck(word : List[int], pattern : List[int]) -> bool:
#     Requires(Acc(list_pred(word)))
#     Requires(Acc(list_pred(pattern)))
#     Ensures(Acc(list_pred(word)))
#     Ensures(Acc(list_pred(pattern)))
#     Ensures(not (Result()) or (Exists(int, lambda d_1_i_:
#         (((0) <= (d_1_i_)) and ((d_1_i_) <= (len(pattern)))) and (IsSubstring(word, pattern, d_1_i_)))))
#     Ensures(not (not(Result())) or (Forall(int, lambda d_2_i_:
#         not (((0) <= (d_2_i_)) and ((d_2_i_) <= (len(pattern)))) or (not(IsSubstring(word, pattern, d_2_i_))))))
#     result = False # type : bool
#     d_3_i_ = int(0) # type : int
#     d_3_i_ = 0
#     while (d_3_i_) <= (len(pattern)):
#         Invariant(Acc(list_pred(word)))
#         Invariant(Acc(list_pred(pattern)))
#         Invariant(((0) <= (d_3_i_)) and ((d_3_i_) <= ((len(pattern)) + (1))))
#         Invariant(Forall(int, lambda d_4_j_:
#             (Implies(((0) <= (d_4_j_)) and ((d_4_j_) < (d_3_i_)), not(IsSubstring(word, pattern, d_4_j_))), [[IsSubstring(word, pattern, d_4_j_)]])))
#         if IsSubstring(word, pattern, d_3_i_):
#             result = True
#             return result
#         d_3_i_ = (d_3_i_) + (1)
#     result = False
#     return result