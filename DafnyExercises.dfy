/*===============================================
   CPSC 360
   Dafny INCX

 ===============================================*/

//Problem 1
method isqrt(n: int) returns (r : int)
{
  var m := 1 ;
  while (m*m <= n)
  {
    m := m + 1 ;
  }
  r := m - 1 ;
}

//Answer
method isqrt(n: int) returns (r : int)
  requires n > 0;
  ensures r > 0;
  ensures (r*r) <= n;
  ensures ((r+1)*(r+1)) > n;
{
  var m := 1 ;
  while (m*m <= n)
  invariant (m-1) * (m-1) <= n;
  {
    m := m + 1 ;
  }
  r := m - 1 ;
}

//Problem 2
function sumTo(a:array<int>, k:nat):int
{
  if (k == 0) then 0 else a[k-1] + sumTo(a, k-1)
}

method sum(a:array<int>) returns (s:int)
{
  var i:nat := 0 ;
  s := 0 ;
  while (i < a.Length)
  {
    s := s + a[i] ;
    i := i + 1 ;
  }
}

//Answer
function sumTo(a:array<int>, k:nat):int
reads a;
requires a != null;
requires k <= a.Length;
{
  if (k == 0) then 0 else a[k-1] + sumTo(a, k-1)
}

method sum(a:array<int>) returns (s:int)
requires a != null;
ensures sumTo(a,a.Length) == s; 
{
  var i:nat := 0 ;
  s := 0 ;
  
  while (i < a.Length)
  invariant i <= a.Length;
  invariant sumTo(a,i) == s;
  {
    s := s + a[i] ;
    i := i + 1 ;
  }

//CountToAndReturnN
// This example uses specifications.  There is a postcondition
// (keyword 'ensures') that says the method is intended to set
// the out-parameter 'r' to 'n'.  Other possible specifications
// are preconditions (keyword 'requires') and loop invariants
// (keyword 'invariant', place just before the open-curly brace
// of the loop body).

// Can you make the program verify?
method M(n: int) returns (r: int)
  ensures r == n
{
  var i := 0;
  while i < n
  {
    i := i + 1;
  }
  r :=

  //Answer
method M(n: int) returns (r: int)
  requires n > 0;
  ensures r == n;
{
  var i := 0;
  while i < n
  invariant i <= n;
  {
    i := i + 1;
  }
  r := i;
}


