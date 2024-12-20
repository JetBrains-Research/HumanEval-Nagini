from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure
def getVal(mx: Optional[int]) -> int:
    # pure-pre-conditions-start
    Requires(mx is not None)  
    # pure-pre-conditions-end

    # pure-start
    return mx  
    # pure-end

def largest__smallest__integers(arr : List[int]) -> Tuple[Optional[int], Optional[int]]:
    # pre-conditions-start
    Requires(Acc(list_pred(arr)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(arr)))
    Ensures(not ((Result()[0]) is None) or (Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(arr)))) or (((arr)[i]) >= (0)))))
    Ensures(not ((Result()[0]) is not None) or ((((Result()[0])) in (arr)) and (((Result()[0])) < (0))))
    Ensures(not ((Result()[0]) is not None) or (Forall(int, lambda i:
        not ((((0) <= (i)) and ((i) < (len(arr)))) and (((arr)[i]) < (0))) or (((arr)[i]) <= (getVal(Result()[0]))))))
    Ensures(not ((Result()[1]) is None) or (Forall(int, lambda i:
        not (((0) <= (i)) and ((i) < (len(arr)))) or (((arr)[i]) <= (0)))))
    Ensures(not ((Result()[1]) is not None) or (((getVal(Result()[1])) in (arr)) and ((getVal(Result()[1])) > (0))))
    Ensures(not ((Result()[1]) is not None) or (Forall(int, lambda i:
        not ((((0) <= (i)) and ((i) < (len(arr)))) and (((arr)[i]) > (0))) or (((arr)[i]) >= (getVal(Result()[1]))))))
    # post-conditions-end

    # impl-start
    a : Optional[int] = None 
    b : Optional[int] = None 
    i = int(0) 
    while (i) < (len(arr)):
        # invariants-start
        Invariant(Acc(list_pred(arr)))
        Invariant(((0) <= (i)) and ((i) <= (len(arr))))
        Invariant(not ((a) is None) or (Forall(int, lambda j:
            not (((0) <= (j)) and ((j) < (i))) or (((arr)[j]) >= (0)))))
        Invariant(Old(a) is None or (Old(a) is not None and Old(a) <= a))
        Invariant(not ((a) is not None) or ((Exists(int, lambda x: x >= 0 and x < i and arr[x] == a)) and ((a) < (0))))
        Invariant(not ((a) is not None) or (Forall(int, lambda j:
            not ((((0) <= (j)) and ((j) < (i))) and (((arr)[j]) < (0))) or (((arr)[j]) <= (getVal(a))))))
        Invariant(not ((b) is None) or (Forall(int, lambda j:
            not (((0) <= (j)) and ((j) < (i))) or (((arr)[j]) <= (0)))))
        Invariant(not ((b) is not None) or (((getVal(b)) in (arr)) and ((getVal(b)) > (0))))
        Invariant(not ((b) is not None) or (Forall(int, lambda j:
            not ((((0) <= (j)) and ((j) < (i))) and (((arr)[j]) > (0))) or (((arr)[j]) >= (getVal(b))))))
        # invariants-end
        if (((arr)[i]) < (0)) and (((a) is None) or (((arr)[i]) >= (a))):
            a = ((arr)[i])
        if (((arr)[i]) > (0)) and (((b) is None) or (((arr)[i]) <= (getVal(b)))):
            b = ((arr)[i])
        i = (i) + (1)
    return (a, b)
    # impl-end
