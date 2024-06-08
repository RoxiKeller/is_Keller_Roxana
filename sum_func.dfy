function mySum(n: nat): nat
    ensures mySum(n) == n * (n + 1) / 2
{
    n * (n + 1) / 2
}
method SumFirstN(n: nat) returns (sum: nat)
  requires n >= 0
  ensures sum==mySum(n)
{
  var i := 0;
  sum := 0;

  while i <= n
    invariant 0 <= i <= n + 1
    invariant sum == i * (i - 1) / 2
    decreases n-i
  {
    sum := sum + i;
    i := i + 1;
  }
}
