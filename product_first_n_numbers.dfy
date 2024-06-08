method Factorial(n: int) returns (product: int)
  requires n >= 0
  ensures product == 
{
  var i := 1;
  product := 1;

  while i <= n
    invariant 1 <= i <= n + 1
    invariant product == (if i == 1 then 1 else (i - 1) * (i - 2) * ... * 1)
  {
    product := product * i;
    i := i + 1;
  }
}
