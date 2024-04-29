// Name: Andrei Tudor Popescu | ID: 1668161
// Name: Alexia Bojian | ID: 1708112

ghost predicate sorted(a: array<int>, lo: nat, hi: nat)
    reads a
    requires 0 <= lo <= hi <= a.Length
{ forall i, j | lo <= i < j < hi :: a[i] <= a[j] }

method SimpleSort(a: array<int>)
    modifies a
    requires a.Length > 0
    ensures sorted(a, 0, a.Length)
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    var p : nat := 0;

    while p != a.Length
        invariant 0 <= p <= a.Length
        invariant sorted(a, 0, p)
        invariant multiset(a[..]) == old(multiset(a[..]))
    {

        var q : nat := 0;
        while q != a.Length
            invariant 0 <= q <= a.Length
            invariant forall i | 0 <= i < q <= a.Length :: a[i] <= a[p]
            invariant sorted(a, 0, p)
            invariant multiset(a[..]) == old(multiset(a[..]))
        {
            if(a[p] < a[q])
            {
                a[p], a[q] := a[q], a[p];
            }
            
            q := q + 1;
        }
        p := p + 1;
    }
}