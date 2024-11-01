## 2D Euclidean Projective Geometric Algebra (PGA) library, where
## Elements represent Lines (vectors) and Points (bivectors).
##
## See [bivector.net](https://bivector.net/tools.html?p=2&q=0&r=1) for more information.
module [
    Multivector,
    zero,
    pi,
    eq,
    s,
    e0,
    e1,
    e2,
    e01,
    e20,
    e12,
    e012,
    scalar,
    line,
    point,
    meet,
    join,
    dot,
    mul,
    add,
    sub,
    smul,
    muls,
    sadd,
    adds,
    ssub,
    subs,
    reverse,
    dual,
    conjugate,
    involute,
    normalize,
]

## Represents a multivector in 2D Euclidian PGA
## s - scalar
## e0 - vector
## e1 - vector
## e2 - vector
## e01 - bivector
## e20 - bivector
## e12 - bivector
## e012 - pseudoscalar
Multivector : {
    s : F32,
    e0 : F32,
    e1 : F32,
    e2 : F32,
    e01 : F32,
    e20 : F32,
    e12 : F32,
    e012 : F32,
}

## An empty multivector with all components set to 0
zero : Multivector
zero = { s: 0.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }

## Helper function for comparing F32 values with tolerance
eqF32 : F32, F32 -> Bool
eqF32 = \i, j ->
    if i > j then i - j < 0.0001 else j - i < 0.0001

## Helper function for comparing Multivectors with tolerance
eq : Multivector, Multivector -> Bool
eq = \x, y ->
    eqF32 x.s y.s
    && eqF32 x.e0 y.e0
    && eqF32 x.e1 y.e1
    && eqF32 x.e2 y.e2
    &&
    eqF32 x.e01 y.e01
    && eqF32 x.e20 y.e20
    && eqF32 x.e12 y.e12
    && eqF32 x.e012 y.e012

pi : F32
pi = 3.14159265358979323846

## Scalar
s : F32 -> Multivector
s = \a -> { s: a, e0: 0.0, e1: 0.0, e2: 0.0, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }

## Basis vector
e0 : F32 -> Multivector
e0 = \b -> { s: 0.0, e0: b, e1: 0.0, e2: 0.0, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }

## Basis vector
e1 : F32 -> Multivector
e1 = \c -> { s: 0.0, e0: 0.0, e1: c, e2: 0.0, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }

## Basis vector
e2 : F32 -> Multivector
e2 = \d -> { s: 0.0, e0: 0.0, e1: 0.0, e2: d, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }

## Basis bivector
e01 : F32 -> Multivector
e01 = \e -> { s: 0.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: e, e20: 0.0, e12: 0.0, e012: 0.0 }

## Basis bivector
e20 : F32 -> Multivector
e20 = \f -> { s: 0.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: 0.0, e20: f, e12: 0.0, e012: 0.0 }

## Basis bivector
e12 : F32 -> Multivector
e12 = \g -> { s: 0.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: 0.0, e20: 0.0, e12: g, e012: 0.0 }

## Basis pseudoscalar
e012 : F32 -> Multivector
e012 = \h -> { s: 0.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: 0.0, e20: 0.0, e12: 0.0, e012: h }

## Scalar
scalar : F32 -> Multivector
scalar = \a -> { s: a, e0: 0.0, e1: 0.0, e2: 0.0, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }

## Line (ax + by + c = 0)
##
## Represented as: a*e1 + b*e2 + c*e0
line : { a : F32, b : F32, c : F32 } -> Multivector
line = \{ a, b, c } -> { s: 0.0, e0: c, e1: a, e2: b, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }

## Euclidian Point (x,y)
##
## Represented as: x*e20 + y*e01 + e12
point : { x : F32, y : F32 } -> Multivector
point = \{ x, y } -> { s: 0.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: y, e20: x, e12: 0.0, e012: 1.0 }

## Meet (wedge, outer product)
## e.g. intersect two Lines to get a Point
meet : Multivector, Multivector -> Multivector
meet = \a, b -> {
    s: b.s * a.s,
    e0: b.e0 * a.s + b.s * a.e0,
    e1: b.e1 * a.s + b.s * a.e1,
    e2: b.e2 * a.s + b.s * a.e2,
    e01: b.e01 * a.s + b.e1 * a.e0 - b.e0 * a.e1 + b.s * a.e01,
    e20: b.e20 * a.s - b.e2 * a.e0 + b.e0 * a.e2 + b.s * a.e20,
    e12: b.e12 * a.s + b.e2 * a.e1 - b.e1 * a.e2 + b.s * a.e12,
    e012: b.e012 * a.s + b.e12 * a.e0 + b.e20 * a.e1 + b.e01 * a.e2 + b.e2 * a.e01 + b.e1 * a.e20 + b.e0 * a.e12 + b.s * a.e012,
}

## Join (vee, regressive product)
## e.g. join two Points to get a Line
join : Multivector, Multivector -> Multivector
join = \a, b -> {
    e012: 1 * (a.e012 * b.e012),
    e12: 1 * (a.e12 * b.e012 + a.e012 * b.e12),
    e20: 1 * (a.e20 * b.e012 + a.e012 * b.e20),
    e01: 1 * (a.e01 * b.e012 + a.e012 * b.e01),
    e2: 1 * (a.e2 * b.e012 + a.e20 * b.e12 - a.e12 * b.e20 + a.e012 * b.e2),
    e1: 1 * (a.e1 * b.e012 - a.e01 * b.e12 + a.e12 * b.e01 + a.e012 * b.e1),
    e0: 1 * (a.e0 * b.e012 + a.e01 * b.e20 - a.e20 * b.e01 + a.e012 * b.e0),
    s: 1 * (a.s * b.e012 + a.e0 * b.e12 + a.e1 * b.e20 + a.e2 * b.e01 + a.e01 * b.e2 + a.e20 * b.e1 + a.e12 * b.e0 + a.e012 * b.s),
}

## Dot (scalar / inner product)
## e.g. dot two Lines to get a scalar
dot : Multivector, Multivector -> Multivector
dot = \a, b -> {
    s: b.s * a.s + b.e1 * a.e1 + b.e2 * a.e2 - b.e12 * a.e12,
    e0: b.e0 * a.s + b.s * a.e0 - b.e01 * a.e1 + b.e20 * a.e2 + b.e1 * a.e01 - b.e2 * a.e20 - b.e012 * a.e12 - b.e12 * a.e012,
    e1: b.e1 * a.s + b.s * a.e1 - b.e12 * a.e2 + b.e2 * a.e12,
    e2: b.e2 * a.s + b.e12 * a.e1 + b.s * a.e2 - b.e1 * a.e12,
    e01: b.e01 * a.s + b.e012 * a.e2 + b.s * a.e01 + b.e2 * a.e012,
    e20: b.e20 * a.s + b.e012 * a.e1 + b.s * a.e20 + b.e1 * a.e012,
    e12: b.e12 * a.s + b.s * a.e12,
    e012: b.e012 * a.s + b.s * a.e012,
}

## Multiply (geometric product)
mul : Multivector, Multivector -> Multivector
mul = \a, b -> {
    s: b.s * a.s + b.e1 * a.e1 + b.e2 * a.e2 - b.e12 * a.e12,
    e0: b.e0 * a.s + b.s * a.e0 - b.e01 * a.e1 + b.e20 * a.e2 + b.e1 * a.e01 - b.e2 * a.e20 - b.e012 * a.e12 - b.e12 * a.e012,
    e1: b.e1 * a.s + b.s * a.e1 - b.e12 * a.e2 + b.e2 * a.e12,
    e2: b.e2 * a.s + b.e12 * a.e1 + b.s * a.e2 - b.e1 * a.e12,
    e01: b.e01 * a.s + b.e1 * a.e0 - b.e0 * a.e1 + b.e012 * a.e2 + b.s * a.e01 + b.e12 * a.e20 - b.e20 * a.e12 + b.e2 * a.e012,
    e20: b.e20 * a.s - b.e2 * a.e0 + b.e012 * a.e1 + b.e0 * a.e2 - b.e12 * a.e01 + b.s * a.e20 + b.e01 * a.e12 + b.e1 * a.e012,
    e12: b.e12 * a.s + b.e2 * a.e1 - b.e1 * a.e2 + b.s * a.e12,
    e012: b.e012 * a.s + b.e12 * a.e0 + b.e20 * a.e1 + b.e01 * a.e2 + b.e2 * a.e01 + b.e1 * a.e20 + b.e0 * a.e12 + b.s * a.e012,
}

## Add
## e.g. add two Lines to get a Line
add : Multivector, Multivector -> Multivector
add = \a, b -> {
    s: a.s + b.s,
    e0: a.e0 + b.e0,
    e1: a.e1 + b.e1,
    e2: a.e2 + b.e2,
    e01: a.e01 + b.e01,
    e20: a.e20 + b.e20,
    e12: a.e12 + b.e12,
    e012: a.e012 + b.e012,
}

## Subtract
## e.g. subtract two Lines to get a Line
sub : Multivector, Multivector -> Multivector
sub = \a, b -> {
    s: a.s - b.s,
    e0: a.e0 - b.e0,
    e1: a.e1 - b.e1,
    e2: a.e2 - b.e2,
    e01: a.e01 - b.e01,
    e20: a.e20 - b.e20,
    e12: a.e12 - b.e12,
    e012: a.e012 - b.e012,
}

## Scalar Multiplication
## e.g. multiply a Line by a scalar
smul : F32, Multivector -> Multivector
smul = \a, b -> {
    s: a * b.s,
    e0: a * b.e0,
    e1: a * b.e1,
    e2: a * b.e2,
    e01: a * b.e01,
    e20: a * b.e20,
    e12: a * b.e12,
    e012: a * b.e012,
}

## Scalar Multiplication
## e.g. multiply a Line by a scalar
muls : Multivector, F32 -> Multivector
muls = \a, b -> {
    s: a.s * b,
    e0: a.e0 * b,
    e1: a.e1 * b,
    e2: a.e2 * b,
    e01: a.e01 * b,
    e20: a.e20 * b,
    e12: a.e12 * b,
    e012: a.e012 * b,
}

## Scalar Addition
## e.g. add a scalar to a Line
sadd : F32, Multivector -> Multivector
sadd = \a, b -> {
    s: a + b.s,
    e0: b.e0,
    e1: b.e1,
    e2: b.e2,
    e01: b.e01,
    e20: b.e20,
    e12: b.e12,
    e012: b.e012,
}

## Scalar Addition
## e.g. add a scalar to a Line
adds : Multivector, F32 -> Multivector
adds = \a, b -> {
    s: a.s + b,
    e0: a.e0,
    e1: a.e1,
    e2: a.e2,
    e01: a.e01,
    e20: a.e20,
    e12: a.e12,
    e012: a.e012,
}

## Scalar Subtraction
## e.g. subtract a scalar from a Line
ssub : F32, Multivector -> Multivector
ssub = \a, b -> {
    s: a - b.s,
    e0: -b.e0,
    e1: -b.e1,
    e2: -b.e2,
    e01: -b.e01,
    e20: -b.e20,
    e12: -b.e12,
    e012: -b.e012,
}

## Scalar Subtraction
## e.g. subtract a scalar from a Line
subs : Multivector, F32 -> Multivector
subs = \a, b -> {
    s: a.s - b,
    e0: a.e0,
    e1: a.e1,
    e2: a.e2,
    e01: a.e01,
    e20: a.e20,
    e12: a.e12,
    e012: a.e012,
}

## Reverse Operator
## Reverse the order of the basis blades
reverse : Multivector -> Multivector
reverse = \a -> {
    s: a.s,
    e0: a.e0,
    e1: a.e1,
    e2: a.e2,
    e01: -a.e01,
    e20: -a.e20,
    e12: -a.e12,
    e012: -a.e012,
}

## Dual (Not) Operator
## Poincare duality operator
dual : Multivector -> Multivector
dual = \a -> {
    s: a.e012,
    e0: a.e12,
    e1: a.e20,
    e2: a.e01,
    e01: a.e2,
    e20: a.e1,
    e12: a.e0,
    e012: a.s,
}

## Conjugate Operator
conjugate : Multivector -> Multivector
conjugate = \a -> {
    s: a.s,
    e0: -a.e0,
    e1: -a.e1,
    e2: -a.e2,
    e01: -a.e01,
    e20: -a.e20,
    e12: -a.e12,
    e012: a.e012,
}

## Involute Operator
involute : Multivector -> Multivector
involute = \a -> {
    s: a.s,
    e0: -a.e0,
    e1: -a.e1,
    e2: -a.e2,
    e01: a.e01,
    e20: a.e20,
    e12: a.e12,
    e012: -a.e012,
}

## Normalize
## e.g. normalize a Line to have a magnitude of 1
normalize : Multivector -> Multivector
normalize = \a ->
    scalarPart = (mul a (conjugate a)).s
    norm = (Num.abs scalarPart)*(Num.abs scalarPart)

    muls a (1.0 / norm)
