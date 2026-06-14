// CompatV2V3.dfy — the compatibility check for the release pair V2 → V3,
// which FAILS: V3 strengthens IndexOf's precondition and weakens Min's
// postcondition. The generated obligations below do not verify (kept as
// comments so the project stays green); instead this file proves their
// NEGATIONS — concrete witnesses that the implications are false — and
// runs them as executable tests. A checker would report: major bump.
//
//   // DOES NOT VERIFY — a caller with |s| > 64 breaks:
//   // lemma IndexOf_PreWeakened(s: seq<int>, x: int)
//   //   requires V2.SeqLib.Sorted(s) && x in s
//   //   ensures  V3.SeqLib.Sorted(s) && x in s && |s| <= 64
//
//   // DOES NOT VERIFY — V3's post no longer pins minimality:
//   // lemma Min_PostStrengthened(s: seq<int>, r: int)
//   //   requires |s| > 0
//   //   requires r in s                                          // V3 ensures
//   //   ensures  r in s && forall i | 0 <= i < |s| :: r <= s[i]  // V2 ensures

include "SeqLibV2.dfy"
include "SeqLibV3.dfy"

module CompatV2V3 {
  import V2
  import V3

  // Witness: a sorted 65-element sequence satisfies V2's precondition but
  // not V3's.
  lemma IndexOf_PreWeakened_Refuted()
    ensures exists s: seq<int>, x: int ::
      (V2.SeqLib.Sorted(s) && x in s)
      && !(V3.SeqLib.Sorted(s) && x in s && |s| <= 64)
  {
    var s := seq(65, i => i);
    assert forall k | 0 <= k < 65 :: s[k] == k;
    assert V2.SeqLib.Sorted(s);
    assert s[0] == 0;
    assert 0 in s;
    assert |s| == 65;
  }

  // Witness: a non-minimal element satisfies V3's postcondition but not
  // V2's.
  lemma Min_PostStrengthened_Refuted()
    ensures exists s: seq<int>, r: int ::
      |s| > 0 && r in s
      && !(r in s && forall i | 0 <= i < |s| :: r <= s[i])
  {
    var s := [1, 2];
    var r := 2;
    assert r in s;
    assert s[0] == 1 && !(r <= s[0]);
  }

  // The same witnesses, executed.
  method {:test} TestV3BreaksIndexOfPre() {
    var s := seq(65, i => i);
    expect V2.SeqLib.Sorted(s) && 0 in s;   // V2's precondition holds ...
    expect !(|s| <= 64);                    // ... V3's added conjunct fails.
  }

  method {:test} TestV3BreaksMinPost() {
    var s := [1, 2];
    var r := 2;
    expect r in s;                                        // V3's post holds ...
    expect !(forall i | 0 <= i < |s| :: r <= s[i]);       // ... V2's fails.
  }
}
