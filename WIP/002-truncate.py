from nagini_contracts.contracts import *

def truncate_number(number: float) -> float:
    Requires(number == number)
    Requires(float("0.0") <= number)
    Ensures(float("0.0") <= number - Result() and number - Result() < float("1.0"))
    # a = int(number) # type : int
    a = float("1.0") # type : float
    return number % a