method Pow(n: int, m: int) returns (r: int)
  requires 0 <= n && 0 <= m
  ensures r == RecPow(n, m)
{
  r := 1;
  var i := 0;
  while i != m
    invariant i <= m && r == RecPow(n, i)
  {
    r := Mul(r, n);
    i := i + 1;
  }
}

function RecPow(n: int, m: int): int
{
  if m <= 0 then 1 else n*RecPow(n, m-1)
}

method Mul(x: int, y: int) returns (r: int)
  requires 0 <= x && 0 <= y
  ensures r == x*y
  decreases x
{
  if x == 0 {
    r := 0;
  } else {
    var m := Mul(x-1, y);
    r := m + y;
  }
}
