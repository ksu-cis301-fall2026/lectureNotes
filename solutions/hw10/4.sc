// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def sumUp(n: Z): Z = {
  Contract(
    Requires (n >= 1, 2 != 0),
    Ensures (Res[Z] == n*(n+1)/2)
  )

  var answer: Z = 0

  if (n == 1)  {
    answer = 1

    Deduce(
      1 ( n == 1 ) by Premise,
      2 ( answer == 1 ) by Premise,
      3 ( answer == n*(n+1)/2 ) by Algebra*(1,2)
    )

  } else {
    Deduce(
      1 ( !(n == 1) ) by Premise, //if condition is false
      2 ( n >= 1 ) by Premise, //from precondition
      3 ( n >= 2 ) by Algebra*(1, 2),
      4 ( n-1 >= 1 ) by Algebra*(3) //proves precondition for recursive call
    )

    answer = sumUp(n-1)

    Deduce(
      1 ( answer == ((n-1)*((n-1)+1))/2 ) by Premise, //postcondition from recursive call
      2 ( answer == ((n-1)*n)/2 ) by Algebra*(1)
    )

    answer = answer + n

    Deduce(
      1 ( answer == Old(answer) + n ) by Premise, //from assignment
      2 ( Old(answer) == ((n-1)*n)/2 ) by Premise, //from previous block
      3 ( answer == ((n-1)*n)/2 + n ) by Subst_<(2, 1),
      4 ( answer == n*(n+1)/2 ) by Algebra*(3)
    )
  }

  Deduce(
      1 ( answer == n*(n+1)/2 ) by Premise //for the postcondition, true in both branches
  )

  return answer
}

//////////// Test code /////////////

var num: Z = 4

Deduce(
  1 ( num == 4 ) by Premise,
  2 ( num >= 1 ) by Algebra*(1), //proves precondition
  3 ( 2 != 0 ) by Algebra T //for division in postcondition
)

val sumTo4: Z = sumUp(num)
println("The sum from 1 up to 4 is ", sumTo4)

Deduce(
  1 ( num == 4 ) by Premise,
  2 ( sumTo4 == num*(num+1)/2 ) by Premise, //from postconditino
  3 ( sumTo4 == 10 ) by Algebra*(1, 2)
)

assert(sumTo4 == 10)

num = 6

Deduce(
  1 ( num == 6 ) by Premise,
  2 ( num >= 1 ) by Algebra*(1) //proves precondition
)

val sumTo6: Z = sumUp(num)
println("The sum from 1 up to 6 is ", sumTo6)

Deduce(
  1 ( num == 6 ) by Premise,
  2 ( sumTo6 == num*(num+1)/2 ) by Premise, //from postconditino
  3 ( sumTo6 == 21 ) by Algebra*(1, 2)
)

assert(sumTo6 == 21)