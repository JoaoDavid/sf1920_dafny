/**
 * Reliable Software
 * Department of Informatics
 * Faculty of Sciences
 * University of Lisbon
 * November 18, 2019
 * João David n49448
 */
method IsPrime (n: nat) returns (b: bool) 
    ensures b <==> prime(n)
    {
    if (n < 2) {
        b := true;
    } else {
        b := true;
        var factor: nat := 2;
        while (b && factor < n)
            invariant b == forall k: int :: 1 < k < factor ==> n % k != 0
            invariant factor <= n;
        {
            if (n % factor == 0) {
                b := false;
            }
            assert b == (n % factor != 0);
            factor := factor + 1;
        }        
    }
    assert b <==> prime(n);
}

function prime (n: nat) : bool {
    forall k: int :: 1 < k < n ==> n % k != 0
}
