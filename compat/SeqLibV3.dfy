// SeqLibV3.dfy — release candidate after 1.1.0, with two BREAKING changes
// (see compat/CompatV2V3.dfy for the failing obligations and witnesses):
//
//   - IndexOf's precondition is *strengthened* (a length cap is added):
//     existing callers with longer sequences no longer verify.
//   - Min's postcondition is *weakened* (minimality dropped): existing
//     callers relying on it no longer verify.
//
// The compatibility checker would assign this release a new major
// version (a new compatibility class / granularity in the calculus).

module V3 {
  module SeqLib {
    predicate Sorted(s: seq<int>) {
      forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
    }

    function IndexOfAny(s: seq<int>, x: int): nat
      requires x in s
      ensures IndexOfAny(s, x) < |s| && s[IndexOfAny(s, x)] == x
    {
      assert s == [s[0]] + s[1..];
      if s[0] == x then 0 else 1 + IndexOfAny(s[1..], x)
    }

    function IndexOf(s: seq<int>, x: int): nat
      requires Sorted(s) && x in s && |s| <= 64   // BREAKING: strengthened
      ensures IndexOf(s, x) < |s| && s[IndexOf(s, x)] == x
    {
      IndexOfAny(s, x)
    }

    function Min(s: seq<int>): int
      requires |s| > 0
      ensures Min(s) in s                          // BREAKING: minimality dropped
    {
      assert s == [s[0]] + s[1..];
      if |s| == 1 then s[0]
      else
        var m := Min(s[1..]);
        if s[0] <= m then s[0] else m
    }

    function Double(x: int): int {
      2 * x
    }

    function Max(s: seq<int>): int
      requires |s| > 0
      ensures Max(s) in s
      ensures forall i | 0 <= i < |s| :: s[i] <= Max(s)
    {
      assert s == [s[0]] + s[1..];
      if |s| == 1 then s[0]
      else
        var m := Max(s[1..]);
        assert forall i | 1 <= i < |s| :: s[i] == s[1..][i-1];
        if s[0] >= m then s[0] else m
    }
  }
}
