method MultipleReturns(n: int)
  returns (j: int)
  requires n > 0
  ensures j >= 0
{
  var i := 0;
  while i < n
    invariant 0 <= i
	decreases n - i
  {
    i := i+1;
  }
  return i;
}
