// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//subtraction by ones
def subByOnes(a: Z, b: Z): Z = {
  Contract(
    Requires( b >= 0 ),
    Ensures( Res[Z] == a-b)
  )

  var answer: Z = a
  var i: Z = 0

  Deduce(
    1 ( answer == a ) by Premise,
    2 ( i == 0 ) by Premise,
    3 ( answer == a - i ) by Algebra*(1, 2) //proves invariant holds before loop begins
  )

  //the invariant holds before the loop begins
  assert(answer == a - i)

  while (i != b) {
    Invariant(
      Modifies(i, answer),
      answer == a - i
    )

    answer = answer - 1

    Deduce(
      1 ( Old(answer) == a - i ) by Premise, //invariant held at beginning of iteration
      2 ( answer == Old(answer) - 1 ) by Premise, //from assignment
      3 ( answer == a - i - 1 ) by Subst_<(1, 2)
    )

    i = i + 1

    Deduce(
      1 ( answer == a - Old(i) - 1 ) by Premise, //from previous block
      2 ( i == Old(i) + 1 ) by Premise, //from assignment
      3 ( Old(i) == i - 1 ) by Algebra*(2),
      4 ( answer == a - i ) by Algebra*(1, 3) //proves invariant holds at end of iteration
    )

    //the invariant holds at the end of the iteration
    assert(answer == a - i)
  }

  Deduce(
    1 ( answer == a - i ) by Premise, //invariant holds after loop ends
    2 ( !(i != b) ) by Premise, //loop condition is false
    3 ( answer == a - b ) by Algebra*(1, 2) //proves postcondition
  )

  return answer
}

//////////// These assertions should hold when you are done /////////////

var test1: Z = 10
var test2: Z = 7

Deduce(
  1 ( test2 == 7 ) by Premise,
  2 ( test2 >= 0 ) by Algebra*(1) //proves precondition
)

var sub: Z = subByOnes(test1, test2)

Deduce(
  1 ( test1 == 10 ) by Premise,
  2 ( test2 == 7 ) by Premise,
  3 ( sub == test1 - test2 ) by Premise, //from postcondition
  4 ( sub == 3 ) by Algebra*(1,2,3)
)

assert(sub == 3)


test1 = 2
test2 = 4

Deduce(
  1 ( test2 == 4 ) by Premise,
  2 ( test2 >= 0 ) by Algebra*(1) //proves precondition
)

sub = subByOnes(test1, test2)

Deduce(
  1 ( test1 == 2 ) by Premise,
  2 ( test2 == 4 ) by Premise,
  3 ( sub == test1 - test2 ) by Premise, //from postcondition
  4 ( sub == -2 ) by Algebra*(1,2,3)
)

assert(sub == -2)