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

def longest(strings : List[List[int]]) -> Optional[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(strings)))
    Requires(Forall(strings, lambda s: Acc(list_pred(s))))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(strings)))
    Ensures(Forall(strings, lambda s: Acc(list_pred(s))))
    Ensures(((Result()) is (None)) == ((len(strings)) == (0)))
    Ensures(Implies(Result() is not None, getVal(Result()) >= 0 and getVal(Result()) < len(strings)))
    Ensures(not ((Result()) is not (None)) or (Forall(int, lambda s:
        not ((s) >= 0 and s < len(strings)) or ((len(strings[getVal(Result())])) >= (len(strings[s]))))))
    Ensures(not (Result() is not None) or (Exists(int, lambda s:
        ((s) >= 0 and s < len(strings)) and ((len(strings[getVal(Result())])) == (len(strings[s]))))))
    Ensures(not ((Result()) is not (None)) or (Forall(int, lambda j:
        (not (((0) <= (j)) and ((j) < (Result()))) or ((len((strings)[j])) < (len(strings[getVal(Result())])))))))
    # post-conditions-end

    # impl-start
    result : Optional[int] = None
    if (len(strings)) != (0):
        i : int = 0
        mx : int = -1
        while (i) < (len(strings)):
            # invariants-start
            Invariant(Acc(list_pred(strings)))
            Invariant(Forall(strings, lambda s: Acc(list_pred(s))))
            Invariant(((i) >= (0)) and ((i) <= (len(strings))))
            Invariant(((mx) == (-1)) == ((result) is (None)))
            Invariant(not ((i) == (0)) or ((mx) == (-1)))
            Invariant(Implies(result is not None, getVal(result) >= 0 and getVal(result) < i))
            Invariant(Implies(result is not None, len(strings[getVal(result)]) == mx))
            Invariant(not ((i) > (0)) or (result is not None))
            Invariant(not ((i) > (0)) or ((mx) == (len(strings[getVal(result)]))))
            Invariant(not (result is not None) or (Forall(int, lambda s:
                not ((s) >= 0 and s < i) or ((len(strings[getVal(result)])) >= (len(strings[s]))))))
            Invariant(not (result is not None) or (Exists(int, lambda s:
                ((s) >= 0 and s < i) and ((len(strings[getVal(result)])) == (len(strings[s]))))))
            Invariant(not ((result) is not (None)) or (Forall(int, lambda j:
                    (not (((0) <= (j)) and ((j) < (result))) or ((len((strings)[j])) < (len(strings[getVal(result)])))))))
            # invariants-end
            if result is None or (len((strings)[i])) > (len(strings[getVal(result)])):
                mx = len((strings)[i])
                result = i
                # assert-start  
                Assert(Forall(int, lambda x: Implies(x >= 0 and x < result, len(strings[result]) > len(strings[x]))))
                # assert-end
            i = (i) + (1)
    return result
    # impl-end
