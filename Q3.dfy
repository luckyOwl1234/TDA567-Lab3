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

*/

