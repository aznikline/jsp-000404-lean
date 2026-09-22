# Averaging narrow bin partitions: a pointwise obstruction

## Conclusion

The proposed pointwise criterion is false, even for a strictly legal
four-center configuration with exactly one saturated anchor. There is a
non-saturated remaining row whose encoding-cube weight equals its actual
weight for every valid partition. No distribution over partitions can
amplify that row by any factor greater than one.

This refutes the sufficient condition
`E[2^empty_i] ≥ (4/3) 2^k_i` for every non-saturated remaining row. It does
not refute the desired capacity bound or a genuinely aggregate argument
that allocates extra slack unevenly between different rows.

## A family for every n ≥ 3

Let `d(t)=(cos(t),sin(t))` and choose

```text
lambda = pi/(n+3/4),  beta = 3*lambda/4,
theta = 7*lambda/10,
alpha = 5*lambda/4,
psi   = 23*lambda/10,
gamma = 9*lambda/8.
```

Set `O=(0,0)`, `P=d(theta)`, and

```text
r = sin(theta)/sin(alpha),
q = sin(alpha-theta)/sin(alpha),
Q = (q,0),
u = r*sin(psi-alpha)/sin(psi-gamma),
v = r*sin(alpha-gamma)/sin(psi-gamma),
R = Q+u*d(gamma) = P-v*d(psi).
```

The last equality is the elementary decomposition of `r*d(alpha)` into
the two ray directions `gamma` and `psi`. All coefficients are positive,
as `0<theta<gamma<alpha<psi<pi`. Also `gamma<pi/2`, so `R` lies in the
first quadrant. Write `tau=arg(R)`. Since

```text
det(P,R) = -v*sin(psi-theta) < 0,
```

we have `0<tau<theta`. Thus all rays from `O` lie in `[0,theta]`, strictly
inside the allowed anchor window `[0,beta]`.

## Exact legality and exponents

The actual triangle angles are:

| Triangle | Angles, in the displayed vertex order |
|---|---|
| OPQ | `theta`, `alpha-theta`, `pi-alpha` |
| PQR | `psi-alpha`, `alpha-gamma`, `pi-psi+gamma` |
| OQR | `tau`, `pi-gamma`, `gamma-tau` |
| OPR | `theta-tau`, `psi-theta`, `pi-psi+tau` |

Every entry is strictly positive. Every entry is strictly below
`pi-lambda`: the large angles subtract respectively `1.25`, `1.175`,
`1.125`, or more than `1.6` times lambda from pi, and all remaining
entries are at most `1.6*lambda < pi-lambda` for `n≥3`.
The configuration is therefore injective, noncollinear in every triple,
and strictly legal.

At `O`, the projective row is `[0,tau,theta]`. Its two small gaps are
less than lambda and its wrap is `(n+1/20)*lambda`, so `k_O=n-1`.

At `P`, the row is exactly `[theta,alpha,psi]`, with gaps

```text
(11/20)*lambda, (21/20)*lambda, (n-17/20)*lambda.
```

The floors are `0,1,n-1`, hence `k_P=n-2` and the defect is two.

At `Q`, the row is `[0,gamma,alpha]`, with gaps
`(9/8)*lambda`, `(1/8)*lambda`, `(n-1/2)*lambda`, again giving `k_Q=n-2`.

At `R`, the row is `[tau,gamma,psi]`. Its first two gaps are below
`2*lambda`, and its wrap is less than `(n-17/20)*lambda`. Therefore
`k_R≤n-2`. Thus `O` is the unique saturated center. These are actual
full direction rows, not abstract admissible rows.

## Why all distributions fail at P

After removing `O`, the two directions in row `P` are `alpha` and `psi`.
Their difference is

```text
psi-alpha = (21/20)*lambda > lambda.
```

No interval bin of width strictly less than lambda can contain both.
There are exactly two remaining directions, so every uniquely assigned
n-bin cover has exactly two active coordinates at `P`. Consequently

```text
empty_P = n-2 = k_P,
2^empty_P = 2^k_P
```

for every valid partition individually, and hence for every probability
distribution over such partitions. The required `4/3` lower bound fails.
This argument is independent of boundary positions, uniformity,
randomization, and behavior at exact grid endpoints; the separation is
strictly larger than lambda.

The ordinary corridor is `[lambda,(n+1/2)*lambda]`, of length
`(n-1/2)*lambda`. Every partition into n intervals of width below lambda
actually has each width above `lambda/2`, since the total width deficits
sum to `lambda/2`. Hence the two directions `gamma,alpha` at `Q` always
fall in the first bin. The cube weights of `P,Q,R` are consequently

```text
2^(n-2), 2^(n-1), 2^(n-2),
```

and their sum is `2^n` for every such partition. The slack is necessarily
concentrated at selected vertices; averaging cannot redistribute it
uniformly to `P`.

## Small exact example and relation to prior work

A particularly transparent degree-based example uses `n=3`,
`lambda=48°`, `theta=36°`, `alpha=60°`, `psi=108°`, `gamma=54°`, with the
same ray-intersection construction. Here `24°<tau<36°`, all triangle
angles are at most `126°<132°`, and the exponents are `(2,1,1,1)`.
The potential is exactly `10`, equal to the high-regime capacity.
The directions at `P` are `60°,108°`, so even their exact lambda
separation forces distinct strict-width bins. The more general family
above makes this separation strict and keeps the anchor fan inside beta.

The rational n=2 four-center example already documented in
`ONE_SATURATED_HIGH_RESEARCH.md` gives the same type of pointwise
obstruction: two of its non-saturated rows always occupy both bins and
have actual weight one. The family here shows this failure is not confined
to the first strip or to a large binary-cluster construction.

## Probe and remaining possibilities

`tools/averaged_bin_packing_probe.py` constructs the general family for
`n=3,4,5,8,12,20`, verifies all actual triangle caps and exponents, and
tests 1,000 nonuniform valid partitions per configuration. It samples
positive width deficits summing to `lambda/2`, so every sampled partition
is valid. In all 6,000 tests, the cube-to-weight ratio at `P` is exactly
one and the cube totals are `2^n`. The probe is floating-point
corroboration; the obstruction above is given by exact angle identities
and strict inequalities, not inferred from sampling.

The following possibilities remain unrefuted:

- An aggregate inequality for expected cube weights, using geometric
  relations between several rows rather than a uniform per-row factor.
- A charging argument sending slack from rows like `Q` to tight rows
  like `P` without requiring each row's own encoding to expand.
- A different encoding that changes the coordinate model, rather than
  just moving the boundaries of n narrow interval bins.

Merely assuming an aggregate inequality equivalent to the desired total
capacity would not supply a proof. No such assumption or new Lean premise
has been added here.
