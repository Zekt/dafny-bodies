procedure F(n: int) returns (r: int)
  ensures 100 < n ==> r > 90;
{
  if (100 < n) {
    r := n - 10;
  } else {
    r := n + 100;
  }
}
