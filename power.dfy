// Name: Andrei Tudor Popescu | ID: 1668161
// Name: Alexia Bojian | ID: 1708112

lemma ExpAddExponent(b: nat, m: nat, n: nat)
  ensures exp(b, m + n) == exp(b, m) * exp(b, n)

lemma ExpSquareBase(b: nat, n: nat)
  ensures exp(b * b, n) == exp(b, 2 * n)

ghost function exp(b: nat, n: nat) : nat
{ if n == 0 then 1 else b * exp (b, n - 1) }


method FastExp (b: nat, n: nat) returns (r: nat)
    ensures r == exp(b, n)
{
    r := 1;
    var i : nat, d : nat := n , b;
    
    while 0 != i
        invariant 0 <= i <= n
        invariant r * exp(d, i) == exp(b, n)
    {
        calc 
        {
            exp(d, i);
            exp(d, 2 * (i / 2) + i % 2);
            {ExpAddExponent(d, 2 * (i / 2), i % 2);}
            exp(d, 2 * (i / 2)) * exp(d, i % 2);
            {ExpSquareBase(d, i / 2); }
            exp(d * d, i / 2) * exp(d, i % 2);
        }

        if i % 2 == 1
        {
            assert exp(d, i % 2) == d;
            r := r * d;
        }
        
        d, i := d * d, i / 2;
    }
}