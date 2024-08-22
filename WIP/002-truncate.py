from nagini_contracts.contracts import *

def truncate_number(number: float) -> float:
    Requires(float("0.0") <= number)
    Ensures(float("0.0") <= number - Result() and number - Result() < float("1.0"))
    return number % float("1.0")