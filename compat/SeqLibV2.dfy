// SeqLibV2.dfy — release 1.1.0 (candidate): the current sources under
// compatibility check against V1. Four kinds of change, all compatible:
//
//   - Sorted is *redefined* (adjacent → pairwise). It appears in
//     IndexOf's precondition, so the checker emits a precondition-
//     weakening obligation V1.Sorted ⇒ V2.Sorted — which needs induction,
//     exercising the manual-proof hook (compat/CompatProofs.dfy).
//   - Min's postcondition is *strengthened* (minimality added):
//     covariant, fine — the obligation is new-post ⇒ old-post.
//   - Double's transparent *body is rewritten* but equivalent: the
//     checker emits a body-equivalence obligation.
//   - Max is *added*: no obligation.

module V2 {
  module SeqLib {
    // Sortedness, now stated pairwise.
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
      requires Sorted(s) && x in s
      ensures IndexOf(s, x) < |s| && s[IndexOf(s, x)] == x
    {
      IndexOfAny(s, x)
    }

    function Min(s: seq<int>): int
      requires |s| > 0
      ensures Min(s) in s
      ensures forall i | 0 <= i < |s| :: Min(s) <= s[i]
    {
      assert s == [s[0]] + s[1..];
      if |s| == 1 then s[0]
      else
        var m := Min(s[1..]);
        assert forall i | 1 <= i < |s| :: s[i] == s[1..][i-1];
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
