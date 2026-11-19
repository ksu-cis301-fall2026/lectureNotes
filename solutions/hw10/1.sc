// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def fourTimes(x: Z, y: Z): Z = {
  Contract(
    Requires(x == y & y > 0),
    Ensures(
      Res[Z] == 4*x,
      Res[Z] >= 4
    )
  )

  var sub: Z = x + y

  Deduce(
    1 ( x == y & y > 0 ) by Premise,
    2 ( sub == x + y ) by Premise,
    3 ( x == y ) by AndE1(1),
    4 ( y > 0 ) by AndE2(1),
    5 ( sub == 2*x ) by Algebra*(2,3),
    6 ( sub >= 2 ) by Algebra*(2,3,4),
    7 ( x > 0 ) by Algebra*(3,4)
  )

  sub = sub * 2

  Deduce(
    1 ( Old(sub) == 2*x ) by Premise,
    2 ( Old(sub) >= 2 ) by Premise,
    3 ( sub == Old(sub)*2 ) by Premise,
    4 ( x > 0 ) by Premise,
    5 ( sub == 4*x ) by Algebra*(1,3,4),
    6 ( sub >= 4 ) by Algebra*(4,5)
  )

  return sub
}

//////////// Test code /////////////

val a: Z = Z.read()
val b: Z = Z.read()

assume(a == 4)
assume(b > 4 & b < 6)

Deduce(
  1 ( a == 4 ) by Premise,
  2 ( b > 4 & b < 6 ) by Premise,
  3 ( b > 4 ) by AndE1(2),
  4 ( b < 6 ) by AndE2(2),
  5 ( b == 5 ) by Algebra*(3,4),
  6 ( a == b-1 ) by Algebra*(1,5),
  7 ( b-1 > 0 ) by Algebra*(5),
  8 ( a == b-1 & b-1 > 0 ) by AndI(6,7)
)

var test: Z = fourTimes(a, b-1)

Deduce(
  1 ( test == 4*a) by Premise,
  2 ( a == 4 ) by Premise,
  3 ( test == 16 ) by Algebra*(1,2)
)

assert(test == 16)


/////////

val j: Z = 7
val k: Z = 4

Deduce(
  1 ( j == 7 ) by Premise,
  2 ( k == 4 ) by Premise,
  3 ( j-3 == k ) by Algebra*(1,2),
  4 ( k > 0 ) by Algebra*(2),
  5 ( j-3 == k & k > 0 ) by AndI(3, 4)
)

test = fourTimes(j-3, k)

Deduce(
  1 ( test == 4*(j-3) ) by Premise,
  2 ( j == 7 ) by Premise,
  3 ( k == 4 ) by Premise,
  5 ( test == 16 ) by Algebra*(1,2,3)
)

assert(test == 16)