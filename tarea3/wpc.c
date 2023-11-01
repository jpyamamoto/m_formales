/*@
  requires -5 <= y <= 5;
  requires -5 <= x <= 5;
  ensures -15 <= \result <= 25;
*/
int function(int x, int y) {
  int res;

  if (x < 0) {
    x = 0;
  }

  if (y < 0) {
    x += 5;
  } else {
    x -= 5;
  }

  res = x - y;
  return res;
}
