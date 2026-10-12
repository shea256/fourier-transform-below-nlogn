#!/usr/bin/env python3
"""Independent rational enclosure of sum H[r]*(r/m)^(1-a)/W.

Uses the positive atanh series with an explicit geometric remainder for log,
then the positive exponential series with an explicit geometric remainder.
No upstream arithmetic engine is imported. Decimal only proposes a bracket;
the two signs of the final bracket are checked using fractions.Fraction.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from functools import lru_cache

GRID = 1 << 224


def down(q):
    return Q(q.numerator * GRID // q.denominator, GRID)


def up(q):
    return -down(-q)


@lru_cache(None)
def log_interval(x):
    x = Q(x)
    assert x >= 1
    k = 0
    while x >= 2:
        x /= 2
        k += 1

    def small(y):
        z = (y - 1) / (y + 1)
        assert 0 <= z <= Q(1, 3)
        total = Q(0)
        power = z
        for j in range(80):
            total += 2 * power / (2 * j + 1)
            power *= z * z
        tail = 2 * power / (161 * (1 - z * z))
        return total, total + tail

    lo, hi = small(x)
    a, b = small(Q(2))
    return down(lo + k * a), up(hi + k * b)


def exp_interval(lo, hi):
    assert 0 <= lo <= hi < Q(1, 10)

    def partial(x):
        total = term = Q(1)
        for j in range(1, 31):
            term *= x / j
            total += term
        return total, term

    low, _ = partial(lo)
    high, last = partial(hi)
    high += last * hi / 31 / (1 - hi / 32)
    return down(low), up(high)


def moment(profile, m, width, saving):
    saving = Q(saving)
    assert 0 <= saving < 1 and m > 1 and width > 0
    low = high = Q(0)
    for r, count in profile.items():
        assert 0 < r < m and count > 0
        l, u = log_interval(Q(m, r))
        l, u = exp_interval(saving * l, saving * u)
        weight = Q(count * r, m * width)
        low += weight * l
        high += weight * u
    return low, high


def decimal(q):
    with localcontext() as ctx:
        ctx.prec = 55
        return str(Decimal(q.numerator) / Decimal(q.denominator))


def certify(profile, m, width):
    with localcontext() as ctx:
        ctx.prec = 50
        terms = [(Decimal(r * n) / Decimal(m * width),
                  (Decimal(m) / Decimal(r)).ln()) for r, n in profile.items()]
        low, high = Decimal(0), Decimal("0.01")
        for _ in range(100):
            a = (low + high) / 2
            if sum(p * (a * l).exp() for p, l in terms) < 1:
                low = a
            else:
                high = a
        grid = 10**15
        tick = int(low * grid)
    left, right = Q(tick, grid), Q(tick + 1, grid)
    l = moment(profile, m, width, left)
    r = moment(profile, m, width, right)
    assert l[1] < 1 < r[0]
    record = Q(2555269, 2500000000)
    at_record = moment(profile, m, width, record)
    return {
        "root_lower": str(left), "root_upper": str(right),
        "root_lower_decimal": decimal(left), "root_upper_decimal": decimal(right),
        "lower_endpoint_margin_at_least": decimal(1 - l[1]),
        "upper_endpoint_excess_at_least": decimal(r[0] - 1),
        "moment_upper_at_dft_record": decimal(at_record[1]),
        "strictly_beats_record_as_a_moment": at_record[1] < 1,
        "method": "80-term rational atanh log; 30-degree rational exponential; explicit tails",
        "scope": "Arithmetic only; no circuit realization or DFT transfer is inferred",
    }
