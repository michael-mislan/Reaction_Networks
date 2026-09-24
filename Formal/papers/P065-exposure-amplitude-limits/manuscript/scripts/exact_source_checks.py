
from fractions import Fraction as F

b = F(1, 10)
d = list(map(F, ['.3', '.3', '.3', '.01', '.3', '.01']))
pairs = [
    [(0, 0, F(1))],
    [(0, 1, F(1, 2)), (1, 0, F(1, 2))],
    [(0, 2, F(1, 4)), (2, 0, F(1, 4)), (1, 1, F(1, 2))],
    [(0, 3, F(1, 2)), (3, 0, F(1, 2))],
    [(0, 4, F(1, 4)), (4, 0, F(1, 4)),
     (1, 3, F(1, 4)), (3, 1, F(1, 4))],
    [(0, 5, F(1, 4)), (5, 0, F(1, 4)), (3, 3, F(1, 2))],
]
L = [[sum(p for j, k, p in terms if j == col)
      for col in range(6)] for terms in pairs]

def mv(M, x):
    return [sum(a*y for a, y in zip(row, x)) for row in M]

def daughter(x, y):
    return [sum(p*x[j]*y[k] for j, k, p in terms) for terms in pairs]

def source(e):
    Q = [[F(0) for _ in range(6)] for _ in range(6)]
    edges = [(0,1,F('.02')), (0,3,F('.02')),
             (1,2,F('.51')), (1,4,F('.01')), (1,0,e), (2,1,2*e),
             (3,5,F('.51')), (3,4,F('.01')), (3,0,e),
             (4,1,e+F('.25')), (4,3,e+F('.25')), (5,3,2*e)]
    for i, j, rate in edges:
        Q[i][j] += rate
        Q[i][i] -= rate
    A = [[Q[i][j] + b*(2*L[i][j]-(i == j))-d[i]*(i == j)
          for j in range(6)] for i in range(6)]
    return Q, A

def phi(e, x):
    qx = mv(source(e)[0], x)
    dx = daughter(x, x)
    return [qx[i]+d[i]*(1-x[i])+b*(dx[i]-x[i]) for i in range(6)]

def det(M):
    M = [row[:] for row in M]
    result = F(1)
    for i in range(len(M)):
        pivot = next((j for j in range(i, len(M)) if M[j][i]), None)
        if pivot is None:
            return F(0)
        if pivot != i:
            M[i], M[pivot] = M[pivot], M[i]
            result = -result
        result *= M[i][i]
        for j in range(i+1, len(M)):
            scale = M[j][i]/M[i][i]
            M[j] = [x-scale*y for x, y in zip(M[j], M[i])]
    return result

coeff = [-5182134, -16495365, 439939800,
         2886960000, 7688000000, 8000000000]
def P(e):
    return sum(F(c)*e**i for i, c in enumerate(coeff))
# Only five rows depend on e, so determinant degree is at most five.
# Six exact evaluations prove the displayed polynomial identity.
for e in map(F, range(6)):
    assert det(source(e)[1]) == P(e)/5000000000
assert P(F('.09275')) < 0 < P(F('.09276'))

w = list(map(F, [14, 11, 10, 84, 43, 107]))
res = [-F('.09')*w[i]-mv(source(e)[1], w)[i]
       for e in [F('.29'), F('.31')] for i in range(6)]
assert min(res) == F('.17')
for q, ends, slack in [
    (['.96','.99','.995','.42','.8','.37'], ['.01','.03'], '.00061'),
    (['.94','.982','.987','.27','.735','.235'],
     ['.0099','.0101'], '.0002')]:
    q = list(map(F, q))
    assert min(-v for e in map(F, ends) for v in phi(e, q)) == F(slack)

def taylor(e):
    Q, _ = source(e)
    linear = [[Q[i][j]-(d[i]+b)*(i == j)
               for j in range(6)] for i in range(6)]
    cs = [[F(0)]*6, d[:]]
    for k in range(1, 4):
        products = [daughter(cs[j], cs[k-j]) for j in range(k+1)]
        lin = mv(linear, cs[k])
        cs.append([(lin[i]+b*sum(p[i] for p in products))/F(k+1)
                   for i in range(6)])
    return cs

lo, hi = taylor(F('.01')), taylor(F('.3'))
assert all(hi[k][2] == lo[k][2] for k in range(4))
assert hi[4][2]-lo[4][2] == -F(49619, 600000000)
# The recurrence makes the fourth coefficient degree at most three in e.
for e in map(F, range(4)):
    assert taylor(e)[4][2] == (-F(16087,8000000)
                              -F(29,480000)*e-F(29,40000)*e*e)
print('Exact determinant, root bracket, certificate slacks, and Taylor checks passed.')
