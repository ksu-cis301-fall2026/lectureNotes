// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def findMin(x: Z, y: Z): Z = {
  Contract(
    //no precondition needed
    Ensures(
      Res[Z] <= x & Res[Z] <= y,    //postcondition 1
      Res[Z] == x | Res[Z] == y     //postcondition 2
    )
  )

  var min: Z = 0

  if (x <= y) {
    min = x

    Deduce(
      1 (     min == x      )   by Premise,
      2 (     min <= x      )   by Algebra*(1),     //need for postcondition 1
      3 (     x <= y        )   by Premise,         //IF condition is true
      4 (     min <= y      )   by Algebra*(1,3)    //need for postcondition 1
    )

  } else {
    min = y

    Deduce(
      1 (     min == y      )   by Premise,
      2 (     !(x <= y)     )   by Premise,         //IF condition is false
      3 (     x > y         )   by Algebra*(2),
      4 (     min <= x      )   by Algebra*(1, 2),  //need for postcondition 1
      5 (     min <= y      )   by Algebra*(1)      //need for postcondition 1
    )
  }

  //prove the postconditions
 Deduce(
    //true in both the if and the else
    1 (     min <= x            )   by Premise,     //need for postcondition 1
    2 (     min <= y            )   by Premise,     //need for postcondition 1
    3 ( min <= x & min <= y     )   by AndI(1, 2),  //proves postcondition 1

    //first was true in if, second true in else
    4 (     min == x | min== y )   by Premise     //proves postcondition 2
  )

  return min
}

////////////// Test code /////////////////

val num1: Z = 6
val num2: Z = 4


val small: Z = findMin(num1, num2)

Deduce(
  1 (   small <= num1 & small <= num2       )   by Premise,     //findMax postcondition 1
  2 (   small == num1 | small == num2       )   by Premise,     //findMax postcondition 2
  3 (   small <= num1                       )   by AndE1(1),
  4 (   small <= num2                       )   by AndE2(1),

  //pull in the initial values
  5 (    num1 == 6                          )   by Premise,
  6 (    num2 == 4                          )   by Premise,

  7 (    small <= 6                         )   by Algebra*(3, 5),
  8 (    small <= 4                         )   by Algebra*(4, 6),
  9 (    small == 6 | small == num2         )   by Subst_<(5, 2),
  10 (   small == 6 | small == 4            )   by Subst_<(6, 9),

  //OR-elimination
  11 SubProof(
    12  Assume( small ==6  ),
    13 (    F               )   by  Algebra*(12, 8),
    14 (    small == 4      )   by  BottomE(13)
  ),
  15 SubProof(
    16 Assume( small == 4   ),
  ),
  17 (  small == 4                          )   by OrE(10,11,15) //needed for assert
)



assert(small == 4)