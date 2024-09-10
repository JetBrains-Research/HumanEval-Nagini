from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def getVal(mx: Optional[int]) -> int:
    # pre-conditions-start
    Requires(mx is not None)  
    # pre-conditions-end

    # impl-start
    return mx  
    # impl-end

def largest__smallest__integers(arr : List[int]) -> Tuple[Optional[int], Optional[int]]:
    # pre-conditions-start
    Requires(Acc(list_pred(arr)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(arr)))
    Ensures(not ((Result()[0]) is None) or (Forall(int, lambda d_0_i_:
        not (((0) <= (d_0_i_)) and ((d_0_i_) < (len(arr)))) or (((arr)[d_0_i_]) >= (0)))))
    Ensures(not ((Result()[0]) is not None) or ((((Result()[0])) in (arr)) and (((Result()[0])) < (0))))
    Ensures(not ((Result()[0]) is not None) or (Forall(int, lambda d_1_i_:
        not ((((0) <= (d_1_i_)) and ((d_1_i_) < (len(arr)))) and (((arr)[d_1_i_]) < (0))) or (((arr)[d_1_i_]) <= (getVal(Result()[0]))))))
    Ensures(not ((Result()[1]) is None) or (Forall(int, lambda d_2_i_:
        not (((0) <= (d_2_i_)) and ((d_2_i_) < (len(arr)))) or (((arr)[d_2_i_]) <= (0)))))
    Ensures(not ((Result()[1]) is not None) or (((getVal(Result()[1])) in (arr)) and ((getVal(Result()[1])) > (0))))
    Ensures(not ((Result()[1]) is not None) or (Forall(int, lambda d_3_i_:
        not ((((0) <= (d_3_i_)) and ((d_3_i_) < (len(arr)))) and (((arr)[d_3_i_]) > (0))) or (((arr)[d_3_i_]) >= (getVal(Result()[1]))))))
    # post-conditions-end

    # impl-start
    a : Optional[int] = None 
    b : Optional[int] = None 
    d_4_i_ = int(0) 
    while (d_4_i_) < (len(arr)):
        # invariants-start
        Invariant(Acc(list_pred(arr)))
        Invariant(((0) <= (d_4_i_)) and ((d_4_i_) <= (len(arr))))
        Invariant(not ((a) is None) or (Forall(int, lambda d_5_j_:
            not (((0) <= (d_5_j_)) and ((d_5_j_) < (d_4_i_))) or (((arr)[d_5_j_]) >= (0)))))
        Invariant(Old(a) is None or (Old(a) is not None and Old(a) <= a))
        Invariant(not ((a) is not None) or ((Exists(int, lambda x: x >= 0 and x < d_4_i_ and arr[x] == a)) and ((a) < (0))))
        Invariant(not ((a) is not None) or (Forall(int, lambda d_6_j_:
            not ((((0) <= (d_6_j_)) and ((d_6_j_) < (d_4_i_))) and (((arr)[d_6_j_]) < (0))) or (((arr)[d_6_j_]) <= (getVal(a))))))
        Invariant(not ((b) is None) or (Forall(int, lambda d_7_j_:
            not (((0) <= (d_7_j_)) and ((d_7_j_) < (d_4_i_))) or (((arr)[d_7_j_]) <= (0)))))
        Invariant(not ((b) is not None) or (((getVal(b)) in (arr)) and ((getVal(b)) > (0))))
        Invariant(not ((b) is not None) or (Forall(int, lambda d_8_j_:
            not ((((0) <= (d_8_j_)) and ((d_8_j_) < (d_4_i_))) and (((arr)[d_8_j_]) > (0))) or (((arr)[d_8_j_]) >= (getVal(b))))))
        # invariants-end
        if (((arr)[d_4_i_]) < (0)) and (((a) is None) or (((arr)[d_4_i_]) >= (a))):
            a = ((arr)[d_4_i_])
        if (((arr)[d_4_i_]) > (0)) and (((b) is None) or (((arr)[d_4_i_]) <= (getVal(b)))):
            b = ((arr)[d_4_i_])
        d_4_i_ = (d_4_i_) + (1)
    return (a, b)
    # impl-end
