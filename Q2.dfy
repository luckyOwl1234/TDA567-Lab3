/*
method Q2(x : int, y : int) returns (big : int, small : int)
  ensures big > small;
{
  if (x > y)
   {big, small := x, y;}
  else
   {big, small := y, x;}
}

1. The program isnt verifiable because the specification doesnt say anything about the parameters
   the method gets.
      e.g. The parameters could be the same which means big will not be bigger than
           small.

2.

    Q ==> wp(S,R)

    Q = empty
    R = big > small
    S = if (x > y) then {big := x, small := y} else {big := y, small := y}

    empty ==> wp(if(x > y) then {big := x, small := y} else {big := y, small := x})

    wp(if(x > y) then {big := x, small := y} else {big := y, small := y}, big > small) =>
    conditional and assignment rule

    Conditional rule:

    ((x > y) ==> wp(big := x && small := y, big > small)) && (!(x > y) ==> wp(big := y && small := x, big > small))

    Assignment rule:

    (x > y ==> x > y) && (x <= y ==> y > x) = true && false = false
*/

//Fixing program:

//1.
method Q2(x : int, y : int) returns (big : int, small : int)
  requires x != y;
  ensures big > small;
{
  if (x > y)
   {big, small := x, y;}
  else
   {big, small := y, x;}
}


//2.
method Q2(x : int, y : int) returns (big : int, small : int)
  ensures big >= small;
{
  if (x > y)
   {big, small := x, y;}
  else
   {big, small := y, x;}
}