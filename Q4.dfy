//1.
method ComputeFact(n : nat) returns (res : nat)
  requires n > 0;
  ensures res == fact(n);
 {
  res := 1;
  var i := 2;
  while (i <= n)
    invariant 2 <= i <= n + 1;
    invariant res == fact(i - 1);
    decreases(n - i);
  {
    res := res * i;
    i := i + 1;
  }
 }

 function fact(n : int) : int
 requires 0 <= n;
 {
     if n == 0 then 1 else n * fact(n - 1)
 }

/*

--------------------------------------------------------------------------------

//2.
** Specification

  wp(while B I D S, R)

  Q: n > 0
  R: res == fact(n)

  B: i <= n
  I: 2 <= i <= n + 1 && res == fact(i - 1)
  D: n - i

  //S1: res := 1
  //S2: i := 2

  //SS1: res := res * i
  //SS2: i := i + 1

  S1: res := res * i
  S2: i := i + 1

** Formula from pdf

  wp(while B I D S, R) =
    I
    && (B && I ==> wp(S, I))
    && (!B && I ==> R)

    && (I ==> D >= 0)
    && (B && I ==>
      wp(tmp := D ; S, tmp > D))




** Substitute with actual values

  wp(while i <= n 2 <= i <= n + 1 && res == fact(i - 1) n - i res := res * i; i := i + 1, res == fact(n)) =
    2 <= i <= n + 1 && res == fact(i - 1)
    && (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> wp(res := res * i; i := i + 1, 2 <= i <= n + 1 && res == fact(i - 1)))
    && (!i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> res == fact(n))

    && (2 <= i <= n + 1 && res == fact(i - 1) ==> n - i >= 0)
    && (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==>
      wp(tmp := n - i ; res := res * i; i := i + 1, tmp > n - i))



** Apply Sequential Rule once

  (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> wp(res := res * i; i := i + 1, 2 <= i <= n + 1 && res == fact(i - 1)))

  (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> wp(res := res * i, wp(i := i + 1, 2 <= i <= n + 1 && res == fact(i - 1))))



** Apply Assignment Rule twice

  (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> wp(res := res * i, wp(i := i + 1, 2 <= i <= n + 1 && res == fact(i - 1))))

  (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> wp(res := res * i, 2 <= i + 1 <= n + 1 && res == fact(i + 1 - 1)))

  (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1 && res * i == fact(i + 1 - 1))



** Simplify // TODO

  (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1 && res * i == fact(i))

  (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1 && fact(i - 1) * i == fact(i))

  (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1 && true // Trivially true

  (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1

  (true && 2 <= i <= n + 1 && res == fact(i - 1)   ==> 2 <= i + 1 <= n + 1 // Has to be true to enter the loop

  (2 <= i <= n + 1 && res == fact(i - 1)           ==> 2 <= i + 1 <= n + 1






** Prove variant bounded below by zero

  I ==> D >= 0

  I: 2 <= i <= n + 1 && res == fact(i - 1)

  Relevant part: i <= n + 1

  i <= (n + 1) ==> (n - i) >= 0
  i - 1 <= n ==> n >= i

  False criteron
  1. i <= (n + 1)
  2. (n - i) < 0

  Ex.
  i = 2
  n = 1






// Early attempt, probably wrong?

** Prove invariant before entering loop

  Q ==> wp(S1, wp(S2, I))

** Substitute with actual values

  Q ==> wp(res := 1, wp(i := 2, 2 <= i <= n + 1 && res == fact(i - 1)))

** Apply Assignment Rule twice

  wp(i := 2, 2 <= i <= n + 1 && res == fact(i - 1)) --> 2 <= 2 <= n + 1 && res == fact(2 - 1)

  wp(res := 1, 2 <= 2 <= n + 1 && res == fact(2 - 1)) --> 2 <= 2 <= n + 1 && 1 == fact(2 - 1))

  Q ==> 2 <= 2 <= n + 1 && 1 == fact(2 - 1))

*/

