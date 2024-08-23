@staticmethod
def freq(s : List[int], x : int) -> int:
    Requires(Acc(list_pred(s)))
    Ensures(Acc(list_pred(s)))
    Ensures(def iife0_():
        coll0_ = set() # type : Set[int]
        compr_0_ = int(0) # type : int
        for compr_0_ in range(0, len(s)):
            d_0_i_: int = compr_0_
            if (((0) <= (d_0_i_)) and ((d_0_i_) < (len(s)))) and (((s)[d_0_i_]) == (x)):
                coll0_ = coll0_.union(set([d_0_i_]))
        return set(coll0_)
    (Result()) == (len(iife0_()
    )))
    count = int(0) # type : int
    count = 0
    d_1_i_ = int(0) # type : int
    d_1_i_ = 0
    def iife1_():
        coll1_ = set() # type : Set[int]
        compr_1_ = int(0) # type : int
        for compr_1_ in range(0, d_1_i_):
            d_3_j_: int = compr_1_
            if (((0) <= (d_3_j_)) and ((d_3_j_) < (d_1_i_))) and (((s)[d_3_j_]) == (x)):
                coll1_ = coll1_.union(set([d_3_j_]))
        return set(coll1_)
    while (d_1_i_) < (len(s)):
        Invariant(Acc(list_pred(s)))
        Invariant(((0) <= (d_1_i_)) and ((d_1_i_) <= (len(s))))
        Invariant((count) == (len(d_2_good_)))
        Invariant((d_2_good_) == (iife1_()
        ))
        if ((s)[d_1_i_]) == (x):
            count = (count) + (1)
        d_1_i_ = (d_1_i_) + (1)
    return count
