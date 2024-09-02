from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

@Pure 
def InArray(lst : List[Tuple[int, int]], i1 : int, j1 : int) -> bool:
    Requires(Acc(list_pred(lst)))
    return Exists(int, lambda i: i >= 0 and i < len(lst) and lst[i] == (i1, j1))

def get_row(lst : List[List[int]], x : int) -> List[Tuple[int, int]]:
    Requires(Acc(list_pred(lst), 1/2))
    Requires(Forall(lst, lambda x: Acc(list_pred(x), 1/2)))
    Ensures(Acc(list_pred(lst), 1/2))
    Ensures(Forall(lst, lambda x: Acc(list_pred(x), 1/2)))
    Ensures(Acc(list_pred(Result()), 1/2))
    Ensures(Forall(int, lambda i: 
        Implies(i >= 0 and i < len(Result()), 0 <= Result()[i][0] and Result()[i][0] < len(lst) and 
            0 <= Result()[i][1] and Result()[i][1] < len(lst[Result()[i][0]]) and
                lst[Result()[i][0]][Result()[i][1]] == x)))
    # Ensures(Forall(int, lambda i: 
    #     Implies(i >= 0 and i < len(lst), 
    #         Forall(int, lambda j: 
    #             Implies(j >= 0 and j < len(lst[i]) and lst[i][j] == x, 
    #                 InArray(Result(), i, j))))))
    
    pos : List[Tuple[int, int]] = []
    i = 0
    while i < len(lst):
        Invariant(Acc(list_pred(lst), 1/2))
        Invariant(Forall(lst, lambda x: Acc(list_pred(x), 1/2)))
        Invariant(Acc(list_pred(pos)))
        Invariant(0 <= i and i <= len(lst))
        Invariant(Forall(int, lambda j: 
            (Implies(j >= 0 and j < len(pos), 0 <= pos[j][0] and pos[j][0] < len(lst) and 
                0 <= pos[j][1] and pos[j][1] < len(lst[pos[j][0]]) and
                    lst[pos[j][0]][pos[j][1]] == x), [[]])))
        # Invariant(Forall(int, lambda i1: 
        #     Implies(i1 >= 0 and i1 < i, 
        #         Forall(int, lambda j1: 
        #             Implies(j1 >= 0 and j1 < len(lst[i]) and lst[i1][j1] == x, 
        #                 InArray(pos, i1, j1))))))
        j = 0
        while j < len(lst[i]):
            Invariant(Acc(list_pred(lst), 1/2))
            Invariant(Forall(lst, lambda x: Acc(list_pred(x), 1/2)))
            Invariant(Acc(list_pred(pos)))
            Invariant(0 <= i and i < len(lst))
            Invariant(0 <= j and j <= len(lst[i]))
            Invariant(Forall(int, lambda j: 
                (Implies(j >= 0 and j < len(pos), 0 <= pos[j][0] and pos[j][0] < len(lst) and 
                    0 <= pos[j][1] and pos[j][1] < len(lst[pos[j][0]]) and
                        lst[pos[j][0]][pos[j][1]] == x), [[]])))
            # Invariant(Forall(int, lambda i1: 
            #     Implies(i1 >= 0 and i1 < i, 
            #         Forall(int, lambda j1: 
            #             Implies(j1 >= 0 and j1 < len(lst[i]) and lst[i1][j1] == x, 
            #                 InArray(pos, i1, j1))))))
            # Invariant(Forall(int, lambda j1: 
            #     (Implies(j1 >= 0 and j1 < j and lst[i][j1] == x, 
            #         InArray(pos, i, j1)), [[InArray(pos, i, j1)]])))
            if lst[i][j] == x:
                pos = pos + [(i, j)]
            j += 1
        i += 1
    return pos