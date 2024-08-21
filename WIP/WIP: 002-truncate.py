from nagini_contracts.contracts import *

def truncate_number(number: float) -> float:
    Requires(0 <= number)
    Ensures(0 <= number - Result() and number - Result() < 1.0)
    return number % 1.0