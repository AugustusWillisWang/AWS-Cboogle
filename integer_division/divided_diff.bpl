// Program: Integer division
// Author: Sergey Velder


//Integer division by successive differences
procedure divided_diff(n, m: int) returns (q, r: int)
   requires  n >= 0  &&  m > 0;
   ensures   0 <= r  &&  r < m;
   ensures   n == m * q + r;
{
   q := 0;  r := n;
   while (r >= m)
      invariant  0 <= r;
      invariant  n == m * q + r;
   {
      r := r - m;
      q := q + 1;
   }
}
