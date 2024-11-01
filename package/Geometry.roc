## 2D Projective Geometric Algebra (PGA) library
module [
    Multivector,
    scalar,
    point,
    line,
    join,
    meet,
    eqMultivector,
    distance,
    normalize,
    rotate,
    scale,
    translate,
    boundingBox,
    isPointInside,
]

## Represents a multivector in 2D PGA with basis elements:
## 1 (scalar)
## e1, e2 (vectors)
## e0 (point at infinity)
## e12, e01, e02 (bivectors)
## e012 (trivector)
Multivector : (F32, F32, F32, F32, F32, F32, F32, F32)

## Helper function for comparing F32 values with tolerance
eqF32 : F32, F32 -> Bool
eqF32 = \a, b -> (a - b) < 0.0001

## Helper function for comparing Multivectors with tolerance
eqMultivector : Multivector, Multivector -> Bool
eqMultivector = \(s1, v11, v12, v13, v14, v15, v16, v17), (s2, v21, v22, v23, v24, v25, v26, v27) ->
    eqF32 s1 s2
    && eqF32 v11 v21
    && eqF32 v12 v22
    && eqF32 v13 v23
    &&
    eqF32 v14 v24
    && eqF32 v15 v25
    && eqF32 v16 v26
    && eqF32 v17 v27

## Scalar in 2D PGA
scalar : F32 -> Multivector
scalar = \s -> (s, 0, 0, 0, 0, 0, 0, 0)

expect eqMultivector (scalar 0) (0, 0, 0, 0, 0, 0, 0, 0)
expect eqMultivector (scalar -1.5) (-1.5, 0, 0, 0, 0, 0, 0, 0)

## Point in 2D PGA
## Represents a point (x,y) as: x*e1 + y*e2 + e0
point : { x : F32, y : F32 } -> Multivector
point = \{ x, y } -> (0, x, y, 1, 0, 0, 0, 0)

expect eqMultivector (point { x: 0, y: 0 }) (0, 0, 0, 1, 0, 0, 0, 0)
expect eqMultivector (point { x: -1, y: 2.5 }) (0, -1, 2.5, 1, 0, 0, 0, 0)

## Line ax + by + c = 0 in 2D PGA
## Represented as: a*e1 + b*e2 + c
line : { a : F32, b : F32, c : F32 } -> Multivector
line = \{ a, b, c } -> (c, a, b, 0, 0, 0, 0, 0)

expect eqMultivector (line { a: 0, b: 1, c: 0 }) (0, 0, 1, 0, 0, 0, 0, 0) # horizontal line y = 0
expect eqMultivector (line { a: 1, b: 0, c: 0 }) (0, 1, 0, 0, 0, 0, 0, 0) # vertical line x = 0

## Join operation - creates a line through two points using the outer product
join : Multivector, Multivector -> Multivector
join = \(_, x1, y1, _, _, _, _, _), (_, x2, y2, _, _, _, _, _) ->
    # For points (x1,y1) and (x2,y2), the line equation is:
    # (y2-y1)x - (x2-x1)y + (x2*y1 - x1*y2) = 0
    a = y2 - y1
    b = -(x2 - x1)
    c = x2*y1 - x1*y2
    (c, a, b, 0, 0, 0, 0, 0)

expect
    # Test vertical line (x = 2)
    p1 = point { x: 2, y: 0 }
    p2 = point { x: 2, y: 5 }
    l = join p1 p2
    (_, a, b, _, _, _, _, _) = l
    eqF32 b 0 && !(eqF32 a 0)

expect
    # Test horitonal line (y = 4)
    p1 = point { x: 2, y: 4 }
    p2 = point { x: -200.12, y: 4 }
    l = join p1 p2
    (_, a, b, _, _, _, _, _) = l
    !(eqF32 b 0) && eqF32 a 0

## Meet operation - finds intersection of two lines using the inner product
meet : Multivector, Multivector -> Multivector
meet = \(s1, v11, v12, _, _, _, _, _), (s2, v21, v22, _, _, _, _, _) ->
    # Compute inner product coefficients
    # Result is a point
    x = v12 * s2 - s1 * v22 # e1 coefficient
    y = s1 * v21 - v11 * s2 # e2 coefficient
    w = v11 * v22 - v12 * v21 # e0 coefficient

    if eqF32 w 0 then
        # Lines are parallel - return point at infinity
        (0, 0, 0, 1, 0, 0, 0, 0)
    else
        # Return normalized point coordinates
        (0, x / w, y / w, 1, 0, 0, 0, 0)

## Test joining two points to create a line
expect
    p1 = point { x: 0, y: 0 }
    p2 = point { x: 1, y: 1 }
    l = join p1 p2
    # Line should have coefficients representing y = x
    eqMultivector l (line { a: 1, b: -1, c: 0 })

## Test finding intersection of two lines
expect
    l1 = line { a: 1, b: -1, c: 0 } # y = x
    l2 = line { a: 1, b: 1, c: -2 } # y = -x + 2
    p = meet l1 l2
    # Intersection should be at (1,1)
    eqMultivector p (point { x: 1, y: 1 })

## Calculate distance between two points
distance : Multivector, Multivector -> F32
distance = \(_, x1, y1, _, _, _, _, _), (_, x2, y2, _, _, _, _, _) ->
    dx = x2 - x1
    dy = y2 - y1
    Num.sqrt (dx * dx + dy * dy)

expect
    p1 = point { x: 0, y: 0 }
    p2 = point { x: 3, y: 4 }
    eqF32 (distance p1 p2) 5

## Normalize a vector to unit length
normalize : Multivector -> Multivector
normalize = \(s, x, y, e0, b1, b2, b3, t) ->
    len = Num.sqrt (x * x + y * y)
    if eqF32 len 0 then
        (s, 0, 0, e0, b1, b2, b3, t)
    else
        (s, x / len, y / len, e0, b1, b2, b3, t)

## Rotate a point around origin by angle (in radians)
rotate : Multivector, F32 -> Multivector
rotate = \(_, x, y, e0, _, _, _, _), angle ->
    cos = Num.cos angle
    sin = Num.sin angle
    newX = x * cos - y * sin
    newY = x * sin + y * cos
    (0, newX, newY, e0, 0, 0, 0, 0)

expect
    p = point { x: 3, y: 4 }
    rotated = rotate p (Num.pi / 2) # 90 degrees
    eqMultivector rotated (point { x: -4, y: 3 })

## Scale a point by sx and sy factors
scale : Multivector, { x : F32, y : F32 } -> Multivector
scale = \(_, x, y, e0, _, _, _, _), factors ->
    (0, x * factors.x, y * factors.y, e0, 0, 0, 0, 0)

## Translate a point by dx and dy
translate : Multivector, { x : F32, y : F32 } -> Multivector
translate = \(_, x, y, e0, _, _, _, _), delta ->
    (0, x + delta.x, y + delta.y, e0, 0, 0, 0, 0)

## Calculate axis-aligned bounding box for a set of points
## Returns {minX, minY, maxX, maxY}
boundingBox : List Multivector -> { minX : F32, minY : F32, maxX : F32, maxY : F32 }
boundingBox = \points ->
    when points is
        [] -> { minX: 0, minY: 0, maxX: 0, maxY: 0 }
        [first, .. as rest] ->
            (_, x, y, _, _, _, _, _) = first
            initialBox = { minX: x, minY: y, maxX: x, maxY: y }

            List.walk rest initialBox \box, (_, px, py, _, _, _, _, _) -> {
                minX: Num.min box.minX px,
                minY: Num.min box.minY py,
                maxX: Num.max box.maxX px,
                maxY: Num.max box.maxY py,
            }

expect
    box = boundingBox [
        point { x: 1, y: 1 },
        point { x: -1, y: 2 },
        point { x: 0, y: -1 },
    ]

    eqF32 box.minX -1
    && eqF32 box.minY -1
    && eqF32 box.maxX 1
    && eqF32 box.maxY 2

## Check if a point is inside a polygon defined by a list of points
isPointInside : Multivector, List Multivector -> Bool
isPointInside = \pnt, polygon ->
    (_, px, py, _, _, _, _, _) = pnt

    # Ray casting algorithm
    List.walkWithIndex polygon Bool.false \inside, vertex, index ->
        nextIndex = (index + 1) % List.len polygon
        (_, x1, y1, _, _, _, _, _) = vertex
        (_, x2, y2, _, _, _, _, _) = List.get polygon nextIndex |> Result.withDefault vertex

        if
            ((y1 > py) != (y2 > py))
            &&
            (px < (x2 - x1) * (py - y1) / (y2 - y1) + x1)
        then
            !inside
        else
            inside

expect
    square = [
        point { x: 0, y: 0 },
        point { x: 2, y: 0 },
        point { x: 2, y: 2 },
        point { x: 0, y: 2 },
    ]
    testPoint = point { x: 1, y: 1 }
    isPointInside testPoint square == Bool.true
