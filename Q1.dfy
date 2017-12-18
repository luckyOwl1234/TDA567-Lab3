
method Abs(x : int) returns (y : int)
  // return value doesn't deviate from intended value
  ensures 0 <= x ==> y == x;
  ensures x < 0 ==> y == -x;
   // return value is greater or equal to zero
  ensures 0 <= y;
{
  if (x < 0)
   { y := -x; }
  else
   { y := x; }
}
/*
1. Because all values of x are handled by the postconditions, there is no need for a precondition.

2.
    Q ==> wp(S,R)

    Q = empty
    R = (0 <= x ==> y == x) && (x < 0 ==> y == -x) && (0 <= y)
    S = if(x < 0) then {y := -x} else {y := x}

    empty ==> wp(if(x < 0) then {y := -x} else {y := x}, (0 <= x ==> y == x) &&
                (x < 0 ==> y == -x) && (0 <= y)) ==> conditional and assignment rule

    Conditional rule:

    ((x < 0) ==> wp(y := -x, (0 <= x ==> y == x) && (x < 0 ==> y == -x) && (0 <= y))) &&
    ((0 <= x) ==> wp(y := x, (0 <= x ==> y == x) && (x < 0 ==> y == -x) && (0 <= y)))

    Assignment rule:

    (x < 0 ==> y := -x) && (0 <= x ==> y := x) = true && true = true

3. It's a "design mistake" because the this method doesnt modify anything and could written as a
   function instead.
*/