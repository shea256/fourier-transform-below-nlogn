"""Small exhaustive exact checks of the generalized frame interface.

Matrices use Gaussian-integer numerators with one explicit power-of-two
denominator. These are finite regression checks of the written general lemma.
"""
from itertools import product


def basis(rows):
    pivots = {}
    for row in rows:
        for bit in sorted(pivots, reverse=True):
            if row >> bit & 1:
                row ^= pivots[bit]
        if row:
            bit = row.bit_length()-1
            for other in pivots:
                if pivots[other] >> bit & 1:
                    pivots[other] ^= row
            pivots[bit] = row
    return tuple(pivots[b] for b in sorted(pivots, reverse=True))


def perp(rows, h):
    return basis(x for x in range(1 << h)
                 if all((x & r).bit_count() % 2 == 0 for r in rows))


def contained(u, v):
    return len(basis(u+v)) == len(v)


def mul(x, y):
    return x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]


def mm(a, b):
    n = len(a)
    out = [[(0, 0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if a[i][k] == (0, 0):
                continue
            for j in range(n):
                if b[k][j] != (0, 0):
                    z = mul(a[i][k], b[k][j])
                    old = out[i][j]
                    out[i][j] = old[0]+z[0], old[1]+z[1]
    return out


def adjoint(a):
    return [[(a[j][i][0], -a[j][i][1]) for j in range(len(a))] for i in range(len(a))]


def representative(u, h):
    """2^h T_U, T_U=K_G C_E K_G^-1, K_G=D_(I+(GG^t)^-1) P_G."""
    n = 1 << h
    columns = list(u)
    for j in range(h):
        if len(basis(tuple(columns)+(1 << j,))) > len(columns):
            columns.append(1 << j)
    # Retain the canonical exact full endpoint F=C^tensor h.
    if len(u) == h:
        columns = [1 << j for j in range(h)]
    perm = []
    for a in range(n):
        out = 0
        for j, col in enumerate(columns):
            if a >> j & 1:
                out ^= col
        perm.append(out)
    inverse = {b: a for a, b in enumerate(perm)}
    assert len(inverse) == n
    matrix = [[((inverse[1 << j] & inverse[1 << k]).bit_count() + (j == k)) % 2
               for k in range(h)] for j in range(h)]
    def phase(a):
        z = sum(matrix[j][j] for j in range(h) if a >> j & 1)
        z += 2*sum(matrix[j][k] for j in range(h) for k in range(j+1, h)
                   if a >> j & 1 and a >> k & 1)
        return z % 4
    roots = ((1, 0), (0, 1), (-1, 0), (0, -1))
    result = [[(0, 0) for _ in range(n)] for _ in range(n)]
    r = len(u)
    for a in range(n):
        for low in range(1 << r):
            b = (a >> r << r) | low
            z = (1 << (h-r), 0)
            for bit in range(r):
                z = mul(z, (1, -1 if (a ^ b) >> bit & 1 else 1))
            z = mul(z, roots[(phase(perm[b])-phase(perm[a])) % 4])
            result[perm[b]][perm[a]] = z
    return result


def verify(h=4):
    spaces = {()}
    for x in range(1, 1 << h):
        spaces |= {basis(u+(x,)) for u in list(spaces)}
    spaces = sorted(spaces, key=lambda u: (len(u), u))
    lag = {u: basis(tuple(x | x << h for x in u) + tuple(x << h for x in perp(u, h)))
           for u in spaces}
    for u in spaces:
        assert len(lag[u]) == h
        transformed = basis((row & ((1 << h)-1)) ^ (row >> h) | (row >> h) << h
                            for row in lag[u])
        assert transformed == lag[perp(u, h)]
    for u, v in product(spaces, repeat=2):
        dim_intersection = len(u)+len(v)-len(basis(u+v))
        distance = len(basis(lag[u]+lag[v]))-h
        assert distance == len(u)+len(v)-2*dim_intersection
    matrices = {u: representative(u, h) for u in spaces}
    scale = 1 << (2*h)
    n = 1 << h
    nested = 0
    for u in spaces:
        for v in spaces:
            if not contained(u, v):
                continue
            transition = mm(matrices[v], adjoint(matrices[u]))
            support = 1 << (len(v)-len(u))
            assert all(sum(transition[i][j] != (0, 0) for i in range(n)) == support
                       for j in range(n))
            if u == v:
                assert all(transition[i][j] == (scale*(i == j), 0)
                           for i in range(n) for j in range(n))
            nested += 1
    full = basis(1 << j for j in range(h))
    f = matrices[full]
    squared = mm(f, f)
    assert all(squared[i][j] == (scale*(i == j ^ (n-1)), 0)
               for i in range(n) for j in range(n)), 'exact full-frame square'
    return {'dimension': h, 'subspaces': len(spaces), 'distance_pairs': len(spaces)**2,
            'exact_nested_transitions': nested, 'full_square_translation': True}
