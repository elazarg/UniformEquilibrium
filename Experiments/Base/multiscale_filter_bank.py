"""E17: a universal finite-polynomial multiscale calendar.

Use lambda_k = 1/log(k+e^2) and an epoch of length k.  For every fixed access
order q, k*lambda_k^q diverges.  For every fixed monitoring order p, the
per-stage bill lambda_k^-p/sqrt(k) vanishes.  This is the finite-order filter
bank underlying the existing universal-calendar calculations.
"""

from __future__ import annotations

import json
import math


def scale(k: int) -> float:
    return 1.0 / math.log(k + math.exp(2.0))


def run() -> dict:
    access_orders = [1, 2, 5, 9]
    monitoring_orders = [1, 3, 7]
    indices = [10**2, 10**3, 10**4, 10**5, 10**6, 10**8, 10**10]

    access_rows = {}
    for order in access_orders:
        values = [k * scale(k) ** order for k in indices]
        # High orders can dip initially, but the last tail is increasing and
        # eventually diverges.
        assert values[-1] > values[-2]
        access_rows[str(order)] = values

    monitoring_rows = {}
    for order in monitoring_orders:
        values = [scale(k) ** (-order) / math.sqrt(k) for k in indices]
        assert values[-1] < values[-2]
        monitoring_rows[str(order)] = values

    # A superpolynomial access probability can escape any theorem stated only
    # for fixed powers: exp(-1/lambda^2) is too rare for the present epoch.
    superpolynomial_access = [
        k * math.exp(-(1.0 / scale(k)) ** 2) for k in indices
    ]
    assert superpolynomial_access[-1] < superpolynomial_access[-2]

    return {
        "experiment": "E17",
        "status": "passed",
        "indices": indices,
        "expected_accesses_per_epoch_by_order": access_rows,
        "monitoring_bill_per_stage_by_order": monitoring_rows,
        "superpolynomial_access_per_epoch": superpolynomial_access,
        "conclusion": (
            "One logarithmically slow calendar handles every fixed finite set of "
            "polynomial access and inverse-power monitoring scales simultaneously."
        ),
        "limitation": (
            "The same calendar need not amplify superpolynomially rare events; an "
            "extension must assume definable rate classes or discover scales adaptively."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
