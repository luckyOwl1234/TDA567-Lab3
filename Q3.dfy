/*
1.
The method isn't allowed to modify variables (e.g. missing modifies clause)
which means it cant update n0 or m0 so it must use local variables. The method
will require modifications of both parameters at some point, hence the need for
local shadows.

--------------------------------------------------------------------------------

2.
Q3 is a multiply method. It's purpose is to multiply two values and return the
answer. It follows that the postcondition should be `ensures res == n0 * m0;`,
i.e. arithmetic multiplication.

--------------------------------------------------------------------------------

3.
*** Definitions

* ==> (implies)
* --> (results in)

* WB --> While guard
* IB --> If guard



*** Specification

Q ==> wp(S, R);

Q := [];

S1: res := 0
S2: n,m := n0, m0
S3: n,m := -n0, -m0
S4: while (0 < n) 

R: res == n0 * m0;

Q ==> wp(S1; S2; S3; S4, R);

Q ==> wp(S1; S2; S3; S4, R);



*** Sequence Rule applied thrice

  Q ==> wp(S1, wp(if IB then S2 else S3, wp(S4, R)));

  wp(while WB I S, R);

  SS1: res := res + m; 
  SS2: n := n - 1;

  WB: n > 0 ;
  I: res + n * m == n0 * m0 // Comparing our local variables (left hand side) to
                            // the calculation of the standard library method
                            // (right hand side)

  wp(while WB I S, R) =
    I
    && (WB && I ==> wp(SS1; SS2, I))
    && (!WB && I ==> R)



*** Substitute with actual statements

  wp(while WB I S, R) =
  res + n * m == n0 * m0
  && (n > 0 && res + n * m == n0 * m0 ==> wp(res := res + m; n := n - 1, res + n * m == n0 * m0))
  && (!n > 0 && res + n * m == n0 * m0 ==> res == n0 * m0)

  wp(res := res + m; n := n - 1, res + n * m == n0 * m0)



*** Sequentual Rule applied once

  wp(res := res + m, wp(n := n - 1, res + n * m == n0 * m0))

  wp(n := n - 1, res + n * m == n0 * m0))



*** Assignment Rule applied once

  wp(n := n - 1, res + n * m == n0 * m0)) --> res + (n - 1) * m == n0 * m0



*** Simplify

  wp(res := res + m, res + (n - 1) * m == n0 * m0)



*** Assignment Rule applied once

  wp(res := res + m, res + (n - 1) * m == n0 * m0) --> (res + m) + (n - 1) * m == n0 * m0



*** Simplify

  wp(res := res + m, res + (n - 1) * m == n0 * m0)
    ==> res + m - m + n * m == n0 * m0
    ==> res + n * m == n0 * m0



*** Recap

  wp(while WB I S, R) =
    res + n * m == n0 * m0
    && (n > 0 && res + n * m == n0 * m0 ==> res + n * m == n0 * m0)
    && (!(n > 0) && res + n * m == n0 * m0 ==> res == n0 * m0)



*** Invariant preservation during loop

  (n > 0 && res + n * m == n0 * m0 ==> res + n * m == n0 * m0)

  Using the following definitions:
    
    A1: n > 0
    A2: res + n * m == n0 * m0 (LHS)
    A3: res + n * m == n0 * m0 (RHS)

  We can deduce that the formula is: A1 && A2 ==> A3
  
  Since A2 == A3, we can simplify:   A1 && A2 ==> A2

  As a direct result, we can see that the boolean evaluation of A1 cannot
  influence the boolean evaluation of the implication.

  Cases:  true  && true  ==> true   [--> true]
          false && true  ==> true   [--> true]
          true  && false ==> false  [--> true]
          false && false ==> false  [--> true]

  The invariant I is hence proved to be preserved during the loop.



*** Invariant preservation after loop

  (!(n > 0) && res + n * m == n0 * m0 ==> res == n0 * m0)

  Simplification:

  ( n <= 0  && res + n * m == n0 * m0 ==> res == n0 * m0)

  Using the following definitions:
    
    A1: n <= 0
    A2: res + n * m == n0 * m0 (LHS)
    A3: res == n0 * m0 (RHS)

  Post-loop state guarantees that n == 0.
 
  This results in (n <= 0 ==> n * m == 0) evaluating to true.

  The invariant I is hence proved to be preserved after the loop.



*** Verify Variant bounded below by zero

  Loop guard: n > 0

  decreases n (n := n - 1)

  Since our loop guard consists of trivial normal, non-inverted logic, we assume verifying it's decrementation to be unnecessary.



*** Recap

  Q ==> wp(S1, wp(if IB then S2 else S3, wp(S4, R)));

  wp(S4, R) --> res + n * m == n0 * m0

  Q ==> wp(S1, wp(if IB then S2 else S3, res + n * m == n0 * m0 && n <= 0 ==> n * m == 0)));

  Q ==> wp(S1, wp(if IB then S2 else S3, res + n * m == n0 * m0 &&  true  ==>   true    )));

  Q ==> wp(S1, wp(if IB then S2 else S3, res + n * m == n0 * m0)));



*** Apply Conditional Rule once

  IB: n0 >= 0
  R: res + n * m == n0 * m0

  wp(if IB then S2 else S3, R) =
    (IB ==> wp(S2, R)) && (!IB ==> wp(S3, R))



*** Substitute with actual values

  wp(if n0 >= 0 then n,m := n0, m0 else n,m := -n0, -m0, res + n * m == n0 * m0) =
    (n0 >= 0 ==> wp(n,m := n0, m0, res + n * m == n0 * m0)) &&
    (!(n0 >= 0) ==> wp(n,m := -n0, -m0, res + n * m == n0 * m0))



*** Simplify


  wp(if n0 >= 0 then n,m := n0, m0 else n,m := -n0, -m0, res + n * m == n0 * m0) =
    (n0 >= 0 ==> wp(n,m := n0, m0, res + n * m == n0 * m0)) &&
    (n0 < 0) ==> wp(n,m := -n0, -m0, res + n * m == n0 * m0))



*** Apply Assignment Rule twice

  R: (n0 >= 0 ==> res + n0 * m0 == n0 * m0) && (n0 < 0) ==> res + -n0 * -m0 == n0 * m0)



*** Substitute with actual values

  Q ==> wp(S1, R)

  [] ==> wp(res := 0, (n0 >= 0 ==> res + n0 * m0 == n0 * m0) && (n0 < 0) ==> res + -n0 * -m0 == n0 * m0)



*** Apply Assignment Rule once

  wp(res := 0, (n0 >= 0 ==> res + n0 * m0 == n0 * m0) && (n0 < 0) ==> res + -n0 * -m0 == n0 * m0)

  ((n0 >= 0) ==> 0 + n0 * m0 == n0 * m0) && ((n0 < 0) ==> 0 + -n0 * -m0 == n0 * m0)



*** Examples

  Case: n0 < 0

    0. ((n0 >= 0) ==> 0 + n0 * m0 == n0 * m0) && ((n0 < 0) ==> 0 + -n0 * -m0 == n0 * m0 )
    1. ((false) ==> 0 + n0 * m0 == n0 * m0)   && ((true) ==> 0 + -n0 * -m0 == n0 * m0   )
    2. (true                                  && ((true) ==> true                       )
    3. (true                                  && (true                                  )
    4. true

  Case: n0 >= 0

    0. ((n0 >= 0) ==> 0 + n0 * m0 == n0 * m0) && ((n0 < 0) ==> 0 + -n0 * -m0 == n0 * m0 )
    1. ((true) ==> 0 + n0 * m0 == n0 * m0)    && ((false) ==> 0 + -n0 * -m0 == n0 * m0  )
    2. ((true) ==> true)                      && (true                                  )
    3. (true                                  && (true                                  )
    4. true



*** Conclusion

  [] ==> true

  Since Q is empty and the implication Q ==> wp(S1, wp(if IB then S2 else S3, wp(S4, R))) evaluates true, Q doesn't require changing preconditions.
*/


method Q3(n0 : int, m0 : int) returns (res : int)
  ensures res == n0 * m0;
{
  var n, m : int;
  res := 0;
  if (n0 >= 0) 
       {n,m := n0, m0;} 
  else 
       {n,m := -n0, -m0;}
  while (0 < n)
    invariant res + n * m == n0 * m0;
    decreases n;
  { 
    res := res + m; 
    n := n - 1; 
  }
}

