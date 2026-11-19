// #Sireum #Logika
//@Logika: --manual 

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def addFive(x: Z): Z = {
  Contract(
    Ensures(
      Res[Z] == x*5
    )
  )

  var total: Z = x

  total = total + x*11

  Deduce(
    1 ( Old(total) == x ) by Premise,
    2 ( total == Old(total) + x*11 ) by Premise,
    3 ( total == 12*x ) by Algebra*(1,2)
  )

  total = total - 7*x

  Deduce(
    1 (Old(total) == 12*x) by Premise,
    2 (total == Old(total) - 7*x) by Premise,
    3 (total == x*5) by Algebra*(1,2)
  )

  return total
}

//////////// Test code /////////////

val a: Z = 8

var addTest: Z = addFive(12-a)

Deduce(
  1 ( addTest == (12-a)*5 ) by Premise,
  2 ( a == 8 ) by Premise,
  3 ( addTest == 20 ) by Algebra*(1,2)
)

assert(addTest == 20)
