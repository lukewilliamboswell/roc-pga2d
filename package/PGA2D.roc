## 2D Euclidean Projective Geometric Algebra (PGA) library, where
## elements represent Lines (vectors) and Points (bivectors).
##
## See [bivector.net](https://bivector.net/tools.html?p=2&q=0&r=1) for more information.
##
## This can be useful for solving common geometric problems in 2D space, such as finding the intersection, union, or distance between lines and points.
## ```roc
## expect
##     # Line <1x + 2y + 3 = 0>
##     line1 = line { a: 1, b: 2, c: 3 }
##
##     # Line <4x + 5y + 6 = 0>
##     line2 = line { a: 4, b: 5, c: 6 }
##
##     # The intersection of the two lines
##     intersection = meet line1 line2
##
##     # equal to the Point <1,-2>
##     eq (normalize intersection) (normalize (point { x: 1, y: -2 }))
## ```
module [
    Multivector,
    zero,
    origin,
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
    idealPoint,
    rotor,
    translator,
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

## A multivector is a general element of the algebra R(2, 0, 1), i.e. 2D Projective Geometric
## Algebra (PGA).
##
## It is basically an 8-element array of the basis elements of 2D PGA. For example, a multivector can be written as:
## ```roc
## a + b*e0 + c*e1 + d*e2 + e*e01 + f*e20 + g*e12 + h*e012
## ```
## Where the basis elements are;
## - `s` Scalar
## - `e0` Vector
## - `e1` Vector
## - `e2` Vector
## - `e01` Bivector
## - `e20` Bivector
## - `e12` Bivector
## - `e012` Trivector / Pseudoscalar
##
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

## An empty multivector with all components zeroed to `0.0`
zero : Multivector
zero = { s: 0.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }

## In PGA, the origin is represented by the e12 bivector.
origin : Multivector
origin = { s: 0.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: 0.0, e20: 0.0, e12: 0.0, e012: 1.0 }

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

## Scalar (grade-0 element)
scalar : F32 -> Multivector
scalar = \a -> { s: a, e0: 0.0, e1: 0.0, e2: 0.0, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }

## Line (grade-1 element) with equation `ax + by + c = 0`
##
## Represented as `a*e1 + b*e2 + c*e0`
line : { a : F32, b : F32, c : F32 } -> Multivector
line = \{ a, b, c } -> { s: 0.0, e0: c, e1: a, e2: b, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }

## Euclidian Point (grade-2 element) with coordinates `x,y`
##
## Represented as: `x*e20 + y*e01 + e12`
point : { x : F32, y : F32 } -> Multivector
point = \{ x, y } -> { s: 0.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: y, e20: x, e12: 1.0, e012: 0.0 }

## Ideal Point (grade-2 element) with coordinates `x,y`
##
## Represented as: `x*e20 + y*e01`
idealPoint : { x : F32, y : F32 } -> Multivector
idealPoint = \{ x, y } -> { s: 0.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: y, e20: x, e12: 0.0, e012: 0.0 }

## A multivector that represents a rotor which performs a rotation
## by `angle` around the center point `cx,cy`
rotor : { angle : F32, cx : F32, cy : F32 } -> Multivector
rotor = \{ angle, cx, cy } ->
    p = point { x: cx, y: cy }
    halfAngle = angle * 0.5
    muls p ((Num.sin halfAngle) + (Num.cos halfAngle))

## A multivector that represents a translator which performs a translation by `dx,dy`
translator : { dx : F32, dy : F32 } -> Multivector
translator = \{ dx, dy } ->
    direction = idealPoint { x: dx, y: -dy }
    add (scalar 1.0) (muls direction 0.5)

## Meet (wedge, outer product)
##
## Used for intersections, e.g. intersect two Lines to get a Point
##
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
##
## Used for joins, e.g. join two Points to get a Line
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
##
## Used for for projections, e.g. dot two Lines to get a scalar
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
##
## Used for Reflections, Rotations, Translations
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
##
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
##
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
##
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
##
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
##
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
##
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
##
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
##
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
##
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
##
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
##
## e.g. normalize a Line to have a magnitude of `1`
normalize : Multivector -> Multivector
normalize = \a ->
    scalarPart = (mul a (conjugate a)).s
    norm = Num.sqrt (Num.abs scalarPart)

    muls a (1.0 / norm)

expect eq (scalar 5.0) { s: 5.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }
expect eq (line { a: 1.0, b: 2.0, c: 3.0 }) { s: 0.0, e0: 3.0, e1: 1.0, e2: 2.0, e01: 0.0, e20: 0.0, e12: 0.0, e012: 0.0 }
expect eq (point { x: 4.0, y: 5.0 }) { s: 0.0, e0: 0.0, e1: 0.0, e2: 0.0, e01: 5.0, e20: 4.0, e12: 1.0, e012: 0.0 }
expect
    line1 = line { a: 0.0, b: 1.0, c: 1.0 } # horizontal line at y + 1 = 0
    line2 = line { a: 1.0, b: -1.0, c: 1.0 } # diagonal line at x - y + 1 = 0
    line3 = add line1 line2 # vertical line at x + 2 = 0
    eq line3 (line { a: 1.0, b: 0.0, c: 2.0 })

# Test geometric product
# (1 + 2e0 + 3e1 + 4e2 + 5e01 + 6e20 + 7e12 + 8e012) * (9 + 10e0 + 11e1 + 12e2 + 13e01 + 14e20 + 15e12 + 16e012)
expect
    a = { s: 1, e0: 2, e1: 3, e2: 4, e01: 5, e20: 6, e12: 7, e012: 8 }
    b = { s: 9, e0: 10, e1: 11, e2: 12, e01: 13, e20: 14, e12: 15, e012: 16 }
    c = { s: -15, e0: -204, e1: 62, e2: 16, e01: 202, e20: 236, e12: 70, e012: 408 }
    d = mul a b
    eq d c

# Test geometric product
# (1 + 2e0 + 3e1 + 4e2 + 5e01 + 6e20 + 7e12 + 8e012) * (-1 -2e0 -3e1 -4e2 -5e01 -6e20 -7e12 -8e012)
expect
    a = { s: 1, e0: 2, e1: 3, e2: 4, e01: 5, e20: 6, e12: 7, e012: 8 }
    b = { s: -1, e0: -2, e1: -3, e2: -4, e01: -5, e20: -6, e12: -7, e012: -8 }
    c = { s: 23, e0: 108, e1: -6, e2: -8, e01: -74, e20: -60, e12: -14, e012: -120 }
    d = mul a b
    eq d c

# Test inner product
# (1 + 2e0 + 3e1 + 4e2 + 5e01 + 6e20 + 7e12 + 8e012)
# (9 + 10e0 + 11e1 + 12e2 + 13e01 + 14e20 + 15e12 + 16e012)
expect
    a = { s: 1, e0: 2, e1: 3, e2: 4, e01: 5, e20: 6, e12: 7, e012: 8 }
    b = { s: 9, e0: 10, e1: 11, e2: 12, e01: 13, e20: 14, e12: 15, e012: 16 }
    c = { s: -15, e0: -204, e1: 62, e2: 16, e01: 218, e20: 204, e12: 78, e012: 88 }
    d = dot a b
    eq d c

# Test outer product
# (1 + 2e0 + 3e1 + 4e2 + 5e01 + 6e20 + 7e12 + 8e012)
# (9 + 10e0 + 11e1 + 12e2 + 13e01 + 14e20 + 15e12 + 16e012)
expect
    a = { s: 1, e0: 2, e1: 3, e2: 4, e01: 5, e20: 6, e12: 7, e012: 8 }
    b = { s: 9, e0: 10, e1: 11, e2: 12, e01: 13, e20: 14, e12: 15, e012: 16 }
    c = { s: 9, e0: 28, e1: 38, e2: 48, e01: 50, e20: 84, e12: 70, e012: 408 }
    d = meet a b
    eq d c

# Test regressive product
# (1 + 2e0 + 3e1 + 4e2 + 5e01 + 6e20 + 7e12 + 8e012)
# (9 + 10e0 + 11e1 + 12e2 + 13e01 + 14e20 + 15e12 + 16e012)
expect
    a = { s: 1, e0: 2, e1: 3, e2: 4, e01: 5, e20: 6, e12: 7, e012: 8 }
    b = { s: 9, e0: 10, e1: 11, e2: 12, e01: 13, e20: 14, e12: 15, e012: 16 }
    c = { s: 408, e0: 104, e1: 152, e2: 152, e01: 184, e20: 208, e12: 232, e012: 128 }
    d = join a b
    eq d c

# Test dual
# (1 + 2e0 + 3e1 + 4e2 + 5e01 + 6e20 + 7e12 + 8e012)
expect
    a = { s: 1, e0: 2, e1: 3, e2: 4, e01: 5, e20: 6, e12: 7, e012: 8 }
    b = dual a
    c = { s: 8, e0: 7, e1: 6, e2: 5, e01: 4, e20: 3, e12: 2, e012: 1 }
    eq b c

# e0*e0 = 0
expect
    a = mul (e0 1) (e0 1)
    b = scalar 0
    eq a b

# e1*e1 = 1
expect
    a = mul (e1 1) (e1 1)
    b = scalar 1
    eq a b

# e2*e2 = 1
expect
    a = mul (e2 1) (e2 1)
    b = scalar 1
    eq a b

# e12*e12 = -1
expect
    a = mul (e12 1) (e12 1)
    b = scalar -1
    eq a b

# e20*e20 = 0
expect
    a = mul (e20 1) (e20 1)
    b = scalar 0
    eq a b

# e01*e01 = 0
expect
    a = mul (e01 1) (e01 1)
    b = scalar 0
    eq a b

# Test normalize
expect
    a = { s: 1, e0: 2, e1: 3, e2: 4, e01: 5, e20: 6, e12: 7, e012: 8 }
    b = { s: 0.2, e0: 0.4, e1: 0.6, e2: 0.8, e01: 1, e20: 1.2, e12: 1.4, e012: 1.6 }
    eq (normalize a) b

expect
    a = { s: -8, e0: -7, e1: -6, e2: -5, e01: -4, e20: -3, e12: -2, e012: -1 }
    res = normalize a
    exp = { s: -3.023715, e0: -2.64575, e1: -2.267786, e2: -1.8898, e01: -1.51185, e20: -1.13389, e12: -0.75592, e012: -0.37796 }
    eq res exp

## Test meet
## (e1 + 2e2 + 3e0) ^ (4e1 + 5e2 + 6e0) = 6e01 - 3e20 - 3e12
expect
    # Line 1x + 2y + 3 = 0
    line1 = line { a: 1, b: 2, c: 3 }

    # Line 4x + 5y + 6 = 0
    line2 = line { a: 4, b: 5, c: 6 }

    # equal to the Point <1,-2> == e20 - 2e01 + e12
    #
    # NOTE the order matters here, if we swapped line1 and line2 we get the negative of the expected result
    # which we could also test for but we would need to compare with (muls exp -1)
    eq (normalize (meet line2 line1)) (normalize (point { x: 1, y: -2 }))
