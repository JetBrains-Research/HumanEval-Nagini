from typing import cast, List, Dict, Set, Optional, Union
from nagini_contracts.contracts import *

def CalculateTriangleArea(a : float, h : float) -> float:
    Requires(((h) >= float("0.0")) and ((a) >= float("0.0")))
    Ensures((Result()) == (((h) * (a)) / (float("2.0"))))
    area = ((h) * (a)) / float("2.0") # type : float
    return area
