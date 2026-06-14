// SeqLibV1.dfy — release 1.0.0 of a small sequence library, as the
// compatibility checker would materialise it: the registry's predecessor
// sources are downloaded and concatenated inside a wrapper module, so its
// declarations live at V1.* without touching the source text itself.
// (A real tool would name the wrapper `Old`; the demo uses V1/V2/V3 so all
// release pairs can coexist in one project.)
//
// See RELATED-WORK.md §2 and compat/CompatV1V2.dfy.

module V1 {
  module SeqLib {
    // Sortedness, stated over adjacent elements.
    predicate Sorted(s: seq<int>) {
      forall i | 0 < i < |s| :: s[i-1] <= s[i]
    }

    function IndexOfAny(s: seq<int>, x: int): nat
      requires x in s
      ensures IndexOfAny(s, x) < |s| && s[IndexOfAny(s, x)] == x
    {
      assert s == [s[0]] + s[1..];
      if s[0] == x then 0 else 1 + IndexOfAny(s[1..], x)
    }

    function IndexOf(s: seq<int>, x: int): nat
      requires Sorted(s) && x in s
      ensures IndexOf(s, x) < |s| && s[IndexOf(s, x)] == x
    {
      IndexOfAny(s, x)
    }

    function Min(s: seq<int>): int
      requires |s| > 0
      ensures Min(s) in s
    {
      assert s == [s[0]] + s[1..];
      if |s| == 1 then s[0]
      else
        var m := Min(s[1..]);
        if s[0] <= m then s[0] else m
    }

    function Double(x: int): int {
      x + x
    }
  }
}
