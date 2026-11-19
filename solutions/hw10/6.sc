// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def sumUp(n: Z): Z = {
  Contract(
    Requires ( n >= 1, 2 != 0 ),
    Ensures (Res[Z] == n*(n+1)/2)
  )

  var sum: Z = 0
  var i: Z = 0

  Deduce(
    1 ( sum == 0 ) by Premise,
    2 ( i == 0 ) by Premise,
    3 ( sum == i*(i+1)/2 ) by Algebra*(1, 2) //proves invariant holds before loop begins
  )

  //the invariant holds before the loop begins
  assert(sum == i * (i+1)/2)

  while (i != n) {
    Invariant(
      Modifies(sum, i),
      sum == (i * (i+1))/2
    )

    i = i + 1

    Deduce(
      1 ( i == Old(i) + 1 ) by Premise, //assignment statement
      2 ( sum == Old(i) * (Old(i) + 1)/2) by Premise, //invariant holds at beginning of iteration
      3 ( sum == (i-1) * i / 2 ) by Algebra*(1, 2)
    )

    sum = sum + i

    Deduce(
      1 ( sum == Old(sum) + i ) by Premise, //assignment statement
      2 ( Old(sum) == (i-1) * i / 2 ) by Premise, //previous block
      3 ( sum == (i-1) * i / 2 + i ) by Subst_<(2, 1),
      4 ( sum == i * (i+1)/2) by Algebra*(3) //proves invariant holds at end of iteration
    )

    //the invariant holds at the end of the iteration
    assert(sum == i * (i+1)/2)
  }

  Deduce(
    1 ( !(i != n) ) by Premise, //loop condition is false
    2 ( sum == i * (i+1)/2) by Premise, //loop invariant holds
    3 ( sum == n*(n+1)/2) by Algebra*(1, 2) //proves postcondition
  )

  return sum
}

//////////// Test code /////////////

var num: Z = 6

Deduce (
  1 ( num == 6 ) by Premise,
  2 ( num >= 1 ) by Algebra*(1),
  3 ( 2 != 0 ) by Algebra T
)

val sumTo6: Z = sumUp(num)
println("The sum from 1 up to 6 is ", sumTo6)

Deduce(
  1 ( num == 6 ) by Premise,
  2 ( sumTo6 == num*(num+1)/2 ) by Premise, //from postcondition
  3 ( sumTo6 == 21 ) by Algebra*(1, 2)
)

assert(sumTo6 == 21)