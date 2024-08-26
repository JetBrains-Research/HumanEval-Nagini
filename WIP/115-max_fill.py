from typing import cast, List, Dict, Set, Optional, Union, Tuple
from nagini_contracts.contracts import *

def max__fill(grid : List[List[int]], capacity : int) -> int:
    Requires(Acc(list_pred(grid), 1/2))
    Requires(Forall(grid, lambda grid0: Acc(list_pred(grid0), 1/2)))
    Requires((capacity) > (0))
    Requires(Forall(int, lambda d_0_i_:
        Forall(int, lambda d_1_j_:
            not ((((0) <= (d_0_i_)) and ((d_0_i_) < (len(grid)))) and (((0) <= (d_1_j_)) and ((d_1_j_) < (len((grid)[d_0_i_]))))) or (((((grid)[d_0_i_])[d_1_j_]) == (0)) or ((((grid)[d_0_i_])[d_1_j_]) == (1))))))
    Ensures(Acc(list_pred(grid), 1/2))
    Ensures(Forall(grid, lambda grid0: Acc(list_pred(grid0), 1/2)))
    # Ensures((Result()) == (psum2(0, len(grid), grid, capacity)))
    cnt = int(0) # type : int
    d_2_i_ = int(0) # type : int
    d_2_i_ = 0
    cnt = 0
    while (d_2_i_) < (len(grid)):
        Invariant(capacity > 0)
        Invariant(Acc(list_pred(grid), 1/2))
        Invariant(Forall(grid, lambda grid0: Acc(list_pred(grid0), 1/2)))
        Invariant(((0) <= (d_2_i_)) and ((d_2_i_) <= (len(grid))))
        # Invariant(Forall(int, lambda d_0_i_: 
        #     (Implies(d_0_i_ >= 0 and d_0_i_ < len(grid), 
        #         psum2(0, d_0_i_ + 1, grid, capacity) == (psum2(0, d_0_i_, grid, capacity) + (psum(0, len(grid[d_0_i_]), grid[d_0_i_]) + capacity - 1) // capacity)), [[]])))
        # Invariant(cnt == (psum2(0, d_2_i_, grid, capacity)))
        Assume(Forall(int, lambda d_0_i_: 
            (Implies(d_0_i_ >= 0 and d_0_i_ < len(grid), 
                psum2(0, d_0_i_ + 1, grid, capacity) == (psum2(0, d_0_i_, grid, capacity) + (psum(0, len(grid[d_0_i_]), grid[d_0_i_]) + capacity - 1) // capacity)), 
                [[grid[d_0_i_]]])))
        d_4_j_ = int(0) # type : int
        d_4_j_ = 0
        d_5_sum__j_ = int(0) # type : int
        d_5_sum__j_ = 0
        while (d_4_j_) < (len((grid)[d_2_i_])):
            Invariant(capacity > 0)
            Invariant(Acc(list_pred(grid), 1/2))
            Invariant(Forall(grid, lambda grid0: Acc(list_pred(grid0), 1/2)))
            Invariant(((0) <= (d_2_i_)) and ((d_2_i_) < (len(grid))))
            Invariant(((0) <= (d_4_j_)) and ((d_4_j_) <= (len((grid)[d_2_i_]))))
            Invariant(Forall(int, lambda d_0_i_: 
                (Implies(d_0_i_ >= 0 and d_0_i_ < len(grid), 
                    psum2(0, d_0_i_ + 1, grid, capacity) == (psum2(0, d_0_i_, grid, capacity) + (psum(0, len(grid[d_0_i_]), grid[d_0_i_]) + capacity - 1) // capacity)), 
                    [[grid[d_0_i_]]])))
            Invariant((psum2(0, d_2_i_ + 1, grid, capacity)) == (psum2(0, d_2_i_, grid, capacity) + (psum(0, len(grid[d_2_i_]), grid[d_2_i_]) + capacity - 1) // capacity))
            # Invariant((psum(0, d_4_j_ + 1, grid[d_2_i_])) == ((psum(0, d_4_j_, grid[d_2_i_]) + (grid[d_2_i_])[d_4_j_])))
            # Invariant(Forall(int, lambda x: 
            #     (not (((0) <= (x)) and ((x) < (len(grid[d_2_i_])))) or 
            #         ((psum(0, x + 1, grid[d_2_i_])) == (psum(0, x, grid[d_2_i_]) + grid[d_2_i_][x])), [[psum(0, x + 1, grid[d_2_i_])]])))
            # Invariant(cnt == (psum2(0, d_2_i_, grid, capacity)))
            # Invariant((d_5_sum__j_) == (psum(0, d_4_j_, grid[d_2_i_])))
            # Assert((psum(0, d_4_j_ + 1, grid[d_2_i_])) == ((psum(0, d_4_j_, grid[d_2_i_]) + (grid[d_2_i_])[d_4_j_])))
            d_5_sum__j_ = (d_5_sum__j_) + (((grid)[d_2_i_])[d_4_j_])
            d_4_j_ = (d_4_j_) + (1)
        d_6_current__el_ = int(0) # type : int
        d_6_current__el_ = ((((d_5_sum__j_) + (capacity)) - (1)) // capacity)
        Assert((psum2(0, d_2_i_ + 1, grid, capacity)) == (psum2(0, d_2_i_, grid, capacity) + (psum(0, len(grid[d_2_i_]), grid[d_2_i_]) + capacity - 1) // capacity))
        cnt = (cnt) + (d_6_current__el_)
        d_2_i_ = (d_2_i_) + (1)
    return cnt

@Pure
def psum2(i : int, j : int, s : List[List[int]], capacity : int) -> int :
    Requires(Acc(list_pred(s), 1/2))
    Requires(Forall(s, lambda x: Acc(list_pred(x), 1/2)))
    Requires(capacity > 0)
    Requires(0 <= i and i <= j and j <= len(s))
    if i == j:
        return 0
    else:
        return ((psum(0, len(s[j - 1]), s[j - 1]) + capacity - 1) // capacity) + (psum2(i, j - 1, s, capacity))
    
@Pure
def psum(i : int, j : int, s : List[int]) -> int :
    Requires(Acc(list_pred(s), 1/2))
    Requires(0 <= i and i <= j and j <= len(s))
    if i == j:
        return 0
    else:
        return (s)[j - 1] + (psum(i, j - 1, s))