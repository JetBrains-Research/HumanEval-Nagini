from typing import List, Tuple
from nagini_contracts.contracts import *

#use-as-unpure
@Pure
def dist(a : int, b : int) -> int :
    # pre-conditions-start
    Ensures(Result() >= 0)
    # pre-conditions-end

    # pure-start
    if (a) < (b):
        return (b) - (a)
    else:
        return (a) - (b)
    # pure-end

def find__closest__elements(s : List[int]) -> Tuple[int, int]:
    # pre-conditions-start
    Requires(Acc(list_pred(s)))
    Requires((len(s)) >= (2))
    # pre-conditions-end
    # post-conditions-start
    Ensures(Acc(list_pred(s)))
    Ensures(len(s) >= 2)
    Ensures(Exists(int, lambda d_0_a_:
        Exists(int, lambda d_1_b_:
            ((0 <= d_0_a_ and d_0_a_ < d_1_b_ and d_1_b_ < len(s)) and ((Result()[0]) == ((s)[d_0_a_])) and (Result()[1]) == ((s)[d_1_b_])))))
    Ensures(Forall(int, lambda d_2_a_:
        Forall(int, lambda d_3_b_:
            Implies((0 <= d_2_a_ and (d_2_a_) < (len(s)) and 0 <= d_3_b_ and d_3_b_ < len(s)) and (d_2_a_ != d_3_b_), (dist(Result()[0], Result()[1])) <= (dist((s)[d_2_a_], (s)[d_3_b_]))))))
    # post-conditions-end

    # impl-start
    l : int = (s)[0]
    h : int = (s)[1]
    d_4_d_ : int = dist(l, h)
    d_5_i_ : int = 0
    # assert-start
    Assert(Exists(int, lambda d_6_a_:
        Exists(int, lambda d_7_b_:
            ((0 <= d_6_a_ and (d_6_a_) < (d_7_b_) and d_7_b_ < len(s))) and ((l) == ((s)[d_6_a_])) and ((h) == ((s)[d_7_b_])))))
    # assert-end
    while (d_5_i_) < (len(s)):
        # invariants-start
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_5_i_)) and ((d_5_i_) <= (len(s))))
        Invariant((d_4_d_) == (dist(l, h)))
        Invariant((len(s)) >= (2))
        Invariant(Exists(int, lambda d_6_a_:
            Exists(int, lambda d_7_b_:
                ((0 <= d_6_a_ and d_6_a_ < d_7_b_ and d_7_b_ < len(s) and ((l) == ((s)[d_6_a_]))) and ((h) == ((s)[d_7_b_]))))))
        Invariant(Forall(int, lambda x: 
            Forall(int, lambda y:
                (Implies((0 <= x and x < len(s) and 0 <= y and y < len(s)), dist(s[x], s[y]) == dist(s[y], s[x])), [[dist(s[x], s[y]) == dist(s[y], s[x])]]))))
        Invariant(Forall(int, lambda d_8_a_:
            Forall(int, lambda d_9_b_:
                (Implies((0 <= d_8_a_ and (d_8_a_) < (d_5_i_) and 0 <= d_9_b_ and d_9_b_ < len(s)) and (d_8_a_ != d_9_b_), (dist(l, h)) <= (dist((s)[d_8_a_], (s)[d_9_b_]))), [[dist((s)[d_8_a_], (s)[d_9_b_])]]))))
        # invariants-end
        d_10_j_ : int = (d_5_i_) + (1)
        # assert-start
        Assert(Forall(int, lambda d_8_a_:
            Forall(int, lambda d_9_b_:
                (Implies((0 <= d_8_a_ and (d_8_a_) < (d_5_i_) and 0 <= d_9_b_ and d_9_b_ < len(s)) and (d_8_a_ != d_9_b_), (dist(l, h)) <= (dist((s)[d_8_a_], (s)[d_9_b_]))), [[dist((s)[d_8_a_], (s)[d_9_b_])]]))))
        Assert(Forall(int, lambda x: (Implies(x >= 0 and x < d_5_i_, dist(l, h) <= dist(s[x], s[d_5_i_])), [[dist(s[x], s[d_5_i_])]])))
        # assert-end
        while (d_10_j_) < (len(s)):
            # invariants-start
            Invariant(Acc(list_pred(s)))
            Invariant(((0) <= (d_5_i_)) and ((d_5_i_) < (len(s))))
            Invariant(((d_5_i_) < (d_10_j_)) and ((d_10_j_) <= (len(s))))
            Invariant((d_4_d_) == (dist(l, h)))
            Invariant((len(s)) >= (2))
            Invariant(Exists(int, lambda d_11_a_:
                Exists(int, lambda d_12_b_:
                    ((((0 <= d_11_a_ and d_11_a_ < d_12_b_ and d_12_b_ < len(s)) ) and ((l) == ((s)[d_11_a_]))) and ((h) == ((s)[d_12_b_]))))))
            Invariant(Forall(int, lambda x: 
                Forall(int, lambda y:
                    (Implies((0 <= x and x < len(s) and 0 <= y and y < len(s)), dist(s[x], s[y]) == dist(s[y], s[x])), [[dist(s[x], s[y]) == dist(s[y], s[x])]]))))
            Invariant(Forall(int, lambda x: (Implies(x >= 0 and x < d_5_i_, dist(s[d_5_i_], s[x]) == dist(s[x], s[d_5_i_])), [[dist(s[d_5_i_], s[x])]])))
            Invariant(Forall(int, lambda x: (Implies(x >= 0 and x < d_5_i_, Implies(dist(l, h) <= dist(s[x], s[d_5_i_]), dist(l, h) <= dist(s[d_5_i_], s[x]))), [[dist(s[d_5_i_], s[x])]])))
            Invariant(Forall(int, lambda x: (Implies(x >= 0 and x < d_5_i_, dist(l, h) <= dist(s[x], s[d_5_i_])), [[dist(s[x], s[d_5_i_])]])))
            Invariant(Forall(int, lambda x: (Implies(x >= 0 and x < d_5_i_, dist(l, h) <= dist(s[d_5_i_], s[x])), [[dist(s[d_5_i_], s[x])]])))
            Invariant(Forall(int, lambda d_13_a_:
                Forall(int, lambda d_14_b_:
                    (Implies((((d_13_a_ == (d_5_i_) and d_5_i_ < d_14_b_ and d_14_b_ < d_10_j_))) and (d_13_a_ != d_14_b_), (dist(l, h)) <= (dist((s)[d_13_a_], (s)[d_14_b_]))), [[dist((s)[d_13_a_], (s)[d_14_b_])]]))))
            Invariant(Forall(int, lambda d_13_a_:
                Forall(int, lambda d_14_b_:
                    (Implies((((d_13_a_ == (d_5_i_) and 0 <= d_14_b_ and d_14_b_ < d_10_j_))) and (d_13_a_ != d_14_b_), (dist(l, h)) <= (dist((s)[d_13_a_], (s)[d_14_b_]))), [[dist((s)[d_13_a_], (s)[d_14_b_])]]))))
            Invariant(Forall(int, lambda d_13_a_:
                Forall(int, lambda d_14_b_:
                    (Implies(((0 <= d_13_a_ and (d_13_a_) < (d_5_i_) and 0 <= d_14_b_ and d_14_b_ < len(s))) and (d_13_a_ != d_14_b_), (dist(l, h)) <= (dist((s)[d_13_a_], (s)[d_14_b_]))), [[dist((s)[d_13_a_], (s)[d_14_b_])]]))))
            # invariants-end
            if d_5_i_ != d_10_j_ and (dist((s)[d_5_i_], (s)[d_10_j_])) <= (d_4_d_):
                l = (s)[d_5_i_]
                h = (s)[d_10_j_]
                d_4_d_ = dist(l, h)
            d_10_j_ = (d_10_j_) + (1)
        # assert-start
        Assert(Forall(int, lambda d_8_a_:
            Forall(int, lambda d_9_b_:
                (Implies((0 <= d_8_a_ and (d_8_a_) <= (d_5_i_) and 0 <= d_9_b_ and d_9_b_ < len(s)) and (d_8_a_ != d_9_b_), (dist(l, h)) <= (dist((s)[d_8_a_], (s)[d_9_b_]))), [[dist((s)[d_8_a_], (s)[d_9_b_])]]))))
        # assert-end
        d_5_i_ = (d_5_i_) + (1)
    return (l, h)
    # impl-end
