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
            //decreases if b then n - factor else 0 - 1;
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

method Main () {
    var factor: bool := IsPrime(2);
    print(factor);
}

