// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function gcd(m: int, n: int): int
    requires m > 0;
    requires n > 0;
    decreases m + n;
{
    if (n == m) then n
    else if (m > n) then gcd(m - n, n)
    else gcd(m, n - m)
}

method euclid(a_m: int, a_n: int) returns (r: int)
    requires a_m > 0 && a_n > 0;
    ensures r == gcd(a_m, a_n);
{
    var m := a_m;
    var n := a_n;
    while (m != n)
		requires n > 0 && m > 0;
        ensures n == gcd(before(m), before(n));
        decreases n + m;
    {
        if (m > n)
        {
            m := m - n;
        }
        else
        {
            n := n - m;
        }
    }
    r := n;
}