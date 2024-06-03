method Fib(n: nat) returns (result: nat)
    requires n >= 0
    ensures result >= 0
    decreases n
{
    if n == 0 || n == 1 {
        result := n;
    } else {
        var f1 := Fib(n - 1);
        var f2 := Fib(n - 2);
        result := f1 + f2;
    }
}

function F(x: int): int 
    //decreases x
{
  if x < 10 then x else F(x - 1)
}

function G(x: int): int 
    //decreases x
{
  if 0 <= x then G(x - 2) else x
}

function H(x: int): int 
    decreases x+60
{
  if x < -60 then x else H(x - 1)
}

function I(x: nat, y: nat): int 
    decreases x,y
{
  if x == 0 || y == 0 then 12
  else if x % 2 == y % 2 then I(x - 1, y)
  else I(x, y - 1)
}

function J(x: nat, y: nat): int 
    decreases x,y
{
  if x == 0 then y
  else if y == 0 then J(x - 1, 3)
  else J(x, y - 1)
}

function K(x: nat, y: nat, z: nat): int 
    decreases x,y,z
{
  if x < 10 || y < 5 then x + y
  else if z == 0 then K(x - 1, y, 5)
  else K(x, y - 1, z - 1)
}

function L(x: int): int 
    decreases 100-x
{
  if x < 100 then L(x + 1) + 10 else x
}
