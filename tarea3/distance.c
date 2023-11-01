#include <limits.h>

/*@
  requires (a < b ==> b - a <= INT_MAX);
  requires (a >= b ==> a - b <= INT_MAX);

  ensures (a < b ==> b == \result + a) &&
          (a >= b ==> b == a - \result);
*/
int distance(int a, int b) {
  if (a < b) return b - a;
  else return a - b;
}
