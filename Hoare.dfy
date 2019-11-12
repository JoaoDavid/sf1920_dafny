method Assignment1 () {
    var m, n, i, r: int;
    assume m >= 0;
    i := m;
    r := n;
    while i > 0
        decreases i - 0;
        invariant r == m + n - i
    {
        r := r + 1;
        i :=  i - 1;
    }
    assert r == m + n;
}