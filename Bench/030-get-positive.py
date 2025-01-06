from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def get__positive(l : List[int]) -> List[int]:
    # pre-conditions-start
    Requires(Acc(list_pred(l)))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(l)))
    Ensures(Acc(list_pred(Result())))
    Ensures(Forall(int, lambda i:
        not (((i) >= (0)) and ((i) < (len(Result())))) or (((Result())[i]) > (0))))
    Ensures((len(Result())) <= (len(l)))
    Ensures(Forall(int, lambda i1:
        not (((i1) >= (0)) and ((i1) < (len(l)))) or (not (((l)[i1]) > (0)) or (Exists(int, lambda i2:
            (((i2) >= (0)) and ((i2) < (len(Result())))) and (((Result())[i2]) == ((l)[i1])))))))
    Ensures(((len(Result())) == (0)) or (Forall(int, lambda i1:
        not (((i1) >= (0)) and ((i1) < (len(Result())))) or (Exists(int, lambda i2:
            (((i2) >= (0)) and ((i2) < (len(l)))) and (((l)[i2]) == ((Result())[i1])))))))
    # post-conditions-end

    # impl-start
    result : List[int] = []
    i : int = 0
    while (i) < (len(l)):
        # invariants-start
        Invariant(Acc(list_pred(result)))
        Invariant(Acc(list_pred(l)))
        Invariant(((i) >= (0)) and ((i) <= (len(l))))
        Invariant((len(result)) <= (i))
        Invariant(Forall(int, lambda i1:
            not (((i1) >= (0)) and ((i1) < (len(result)))) or (((result)[i1]) > (0))))
        Invariant(not ((i) > (0)) or (not (((l)[(i) - (1)]) > (0)) or (Exists(int, lambda i2:
            (((i2) >= (0)) and ((i2) < (len(result)))) and (((result)[i2]) == ((l)[(i) - (1)]))))))
        Invariant(Forall(int, lambda i1:
            not (((i1) >= (0)) and ((i1) < (i))) or (not (((l)[i1]) > (0)) or (Exists(int, lambda i2:
                (((i2) >= (0)) and ((i2) < (len(result)))) and (((result)[i2]) == ((l)[i1])))))))
        Invariant(((len(result)) == (0)) or (Forall(int, lambda i1:
            not (((i1) >= (0)) and ((i1) < (len(result)))) or (Exists(int, lambda i2:
                (((i2) >= (0)) and ((i2) < (len(l)))) and (((l)[i2]) == ((result)[i1])))))))
        # invariants-end
        n : int = (l)[i]
        if (n) > (0):
            res__prev = result
            # assert-start
            Assert(Forall(int, lambda i1:
                not (((i1) >= (0)) and ((i1) < (i))) or (not (((l)[i1]) > (0)) or (Exists(int, lambda i2:
                    (((i2) >= (0)) and ((i2) < (len(result)))) and (((result)[i2]) == ((l)[i1])))))))
            # assert-end
            result = (result) + ([n])
            # assert-start
            Assert(((result)[(len(result)) - (1)]) == (n))
            Assert(Forall(int, lambda i1:
                not (((i1) >= (0)) and ((i1) < (len(res__prev)))) or (((res__prev)[i1]) == ((result)[i1]))))
            Assert(Forall(int, lambda i1:
                not (((i1) >= (0)) and ((i1) < (i))) or (not (((l)[i1]) > (0)) or (Exists(int, lambda i2:
                    (((i2) >= (0)) and ((i2) < (len(res__prev)))) and (((res__prev)[i2]) == ((l)[i1])))))))
            # assert-end
        i = (i) + (1)
    return result
    # impl-end
