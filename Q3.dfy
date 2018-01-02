/*
1.
The method isn't allowed to modify variables (e.g. missing modifies clause)
which means it cant update n0 or m0 so it must use local variables. The method
will require modifications of both parameters at some point, hence the need for
local shadows.

2.
Q3 is a multiply method. It's purpose is to multiply two values and return the
answer. It follows that the postcondition should be `ensures res == n0 * m0;`,
i.e. arithmetic multiplication.

3.
Q ==> wp(S, R);

Q := [];

S1: res := 0;
S2: if (n0 >= 0) {n,m := n0, m0;} 
S3: else {n,m := -n0, -m0;}
S4: while (0 < n) 

R: res == n0 * m0;

Q ==> wp(S1; S2; S3; S4, R);

Q ==> wp(S1; S2; S3; S4, R);

* Sequence Rule applied thrice

Q ==> wp(S1, wp(S2, wp(S3, wp(S4, R))));

wp(while B I S, R);

SS1: res := res + m; 
SS2: n := n - 1;

B: n > 0 ;
I: res + n * m == n0 * m0 // Comparing our local variables (left hand side) to
                          // the calculation of the standard library method
                          // (right hand side)

wp(while B I S, R) =
  I
  && (B && I ==> wp(SS1; SS2, I))
  && (!B && I ==> R)

* Substitute with actual statements

wp(while B I S, R) =
  res + n * m == n0 * m0
  && (n > 0 && res + n * m == n0 * m0 ==> wp(res := res + m; n := n - 1, res + n * m == n0 * m0))
  && (!n > 0 && res + n * m == n0 * m0 ==> res == n0 * m0)

wp(res := res + m; n := n - 1, res + n * m == n0 * m0)

* Sequentual Rule applied once

wp(res := res + m, wp(n := n - 1, res + n * m == n0 * m0))

wp(n := n - 1, res + n * m == n0 * m0))

* Assignment Rule applied once

wp(n := n - 1, res + n * m == n0 * m0)) ==> res + (n - 1) * m == n0 * m0

* Simplify

wp(res := res + m, res + (n - 1) * m == n0 * m0)

* Assignment Rule applied once

wp(res := res + m, res + (n - 1) * m == n0 * m0) ==> (res + m) + (n - 1) * m == n0 * m0

* Simplify

wp(res := res + m, res + (n - 1) * m == n0 * m0
  ==> res + m - m + n * m == n0 * m0
  ==> res + n * m == n0 * m0

* Recap

wp(while B I S, R) =
  res + n * m == n0 * m0
  && (n > 0 && res + n * m == n0 * m0 ==> res + n * m == n0 * m0
  && (!(n > 0) && res + n * m == n0 * m0 ==> res == n0 * m0)







// wp(while n > 0 [] while (0 < n) { res := res + m; n := n - 1; }, res == n0 * m0;

*/


method Q3(n0 : int, m0 : int) returns (res : int)
  
{
  var n, m : int;
  res := 0;
  if (n0 >= 0) 
       {n,m := n0, m0;} 
  else 
       {n,m := -n0, -m0;}
  while (0 < n) 
  { 
    res := res + m; 
    n := n - 1; 
  }
}


