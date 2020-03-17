// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Count(a_to: int) returns (r: int)
	requires a_to >= 0;
	ensures r == a_to;
    ensures r == before(a_to);
	{
		var x,y: int;
		x := 0;
		y := before(x);

		while(x < a_to)
			requires a_to >= x;
			ensures x == a_to;
        {
            x := x + 1;
            y := before(x) + 1;
        }
		r := x;
	}