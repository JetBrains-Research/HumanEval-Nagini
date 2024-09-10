from nagini_contracts.contracts import *

def cube__root(N : int) -> int:
    Requires((N) >= (0))
    Ensures((N) >= (0))
    Ensures(Result() >= 0)
    Ensures(((cube(Result())) <= (N)) and ((N) < (cube((Result()) + (1)))))
    Ensures((Result()) <= (N))
    # Ensures(Forall(int, lambda d_0_r_: Implies(r < d_0_r_ and d_0_r_ <= N, cube(d_0_r_) > N)))
    # Ensures(Forall(int, lambda d_0_r_: Implies(0 <= d_0_r_ and d_0_r_ < r, cube(d_0_r_) < N)))
    r = int(0) # type : int
    r = 0
    # Assert(Forall(int, lambda x: x < (x + 1)))
    # Assert(Forall(int, lambda x: Implies(0 <= x and x < N, x * x < (x + 1) * (x + 1))))
    # Assert(Forall(int, lambda x: x * x * x < (x + 1) * (x + 1) * (x + 1)))
    # Assert(Forall(int, lambda x: (Implies(0 <= x and x < N, cube(x) < cube(x + 1)), [[cube(x)]])))
    while (cube((r) + (1))) <= (N):
        Invariant(N >= 0)
        Invariant(r >= 0 and r <= N)
        Invariant((cube(r)) <= (N))
        Invariant(Forall(int, lambda x: (Implies(0 <= x and x <= N, cube_less(x, x + 1)), [[cube_less(x, x + 1)]])))
        Invariant(Forall(int, lambda x: (Implies(0 <= x and x < r, cube_less(x, r)), [[cube_less(x, r)]])))
        # Invariant(Forall(int, lambda x: 
        #     (Implies(0 <= x and x < r, cube(x) < N)), [[cube(x)]]))
        # Invariant(Forall(int, lambda x: (Implies(0 <= r and r < x and x <= N, cube_less(r, x)), [[cube_less(r, x)]])))
        # Invariant(cube_less(r, r + 1))
        # Invariant(Forall(int, lambda x: 
        #     (Implies(0 <= x and x <= N, 
        #         Forall(int, lambda y : 
        #             (Implies(x < y and y <= N, 
        #                 cube_less(x, y)), [[cube(y)]]))), 
        #     [[cube(x)]])))
        Invariant(Forall(int, lambda x: 
            (Implies(0 <= x and x <= N, 
                cubes_less(x, N)), 
            [[cubes_less(x, N)]])))
        # Invariant(Forall(int, lambda d_0_r_: (Implies(0 <= d_0_r_ and d_0_r_ < r, cube(d_0_r_) < N), [[cube(d_0_r_)]])))
        # Assert(cube_less(r, r + 1))
        r = (r) + (1)
    return r

@Pure
def cubes_less(x : int, N : int) -> bool:
    Requires(0 <= x and x <= N)
    return Forall(int, lambda y : (Implies(x < y and y <= N, cube_less(x, y)), [[cube_less(x, y)]]))

@Pure
def cube_less(a : int, b : int) -> bool:
    Requires(a >= 0)
    Requires(b >= 0)
    return cube(a) < cube(b)

def is__cube(n : int) -> bool:
    Requires(n >= (0))
    Ensures((n) >= (0))
    Ensures(Implies(Result(), Exists(int, lambda d_0_r_:
        (((0) <= (d_0_r_)) and ((d_0_r_) <= (n))) and ((n) == (cube(d_0_r_))))))
    # Ensures(Implies(not(Result()), Forall(int, lambda d_1_r_:
    #     Implies(((0) <= (d_1_r_)) and ((d_1_r_) <= (n)), (n) != (cube(d_1_r_))))))
    r = False # type : bool
    d_2_root_ = int(0) # type : int
    out0_ = cube__root(n) # type : int
    d_2_root_ = out0_
    if (cube(d_2_root_)) == (n):
        r = True
    elif True:
        r = False
    return r

@Pure
def cube(n : int) -> int :
    Requires(n >= 0)
    Ensures(Result() >= 0)
    return ((n) * (n)) * (n)