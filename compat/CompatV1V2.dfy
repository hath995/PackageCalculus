// CompatV1V2.dfy — the GENERATED compatibility obligations for the
// release pair V1 → V2 (the file a checker would emit; here written by
// hand to pin down the convention; see RELATED-WORK.md §2).
//
// Generation rules per exported declaration:
//   - signature changed in types        → the obligation would not even
//                                         resolve: automatic major bump;
//   - contract ASTs unchanged (over the shared vocabulary) → skipped;
//   - requires changed                  → PreWeakened obligation:
//                                           old-pre ⇒ new-pre;
//   - ensures changed                   → PostStrengthened obligation:
//                                           old-pre ∧ new-post ⇒ old-post,
//                                         with the result as a bound
//                                         variable;
//   - transparent body changed          → BodyEquivalent obligation;
//   - declaration added                 → no obligation;
//   - declaration removed from exports  → major bump (not shown here).
//
// Bodies default to `{}`; where the author has supplied
// `<Obligation>_Manual` in compat/CompatProofs.dfy, the generator calls it.
//
// VERDICT: this whole file verifies ⟹ V2 is contract-compatible with V1
// ⟹ same compatibility class (a minor bump; same granularity g in the
// calculus, so min-bound resolution may float across it).

include "SeqLibV1.dfy"
include "SeqLibV2.dfy"
include "CompatProofs.dfy"

module CompatV1V2 {
  import V1
  import V2
  import CompatProofsV1V2

  // IndexOf — requires changed (Sorted was redefined): old-pre ⇒ new-pre.
  // Discharged via the author's manual induction proof.
  lemma IndexOf_PreWeakened(s: seq<int>, x: int)
    requires V1.SeqLib.Sorted(s) && x in s
    ensures V2.SeqLib.Sorted(s) && x in s
  {
    CompatProofsV1V2.IndexOf_PreWeakened_Manual(s, x);
  }

  // IndexOf — ensures unchanged over the shared vocabulary: skipped.

  // Min — requires unchanged: skipped.
  // Min — ensures strengthened: old-pre ∧ new-post ⇒ old-post, with the
  // result spliced in as the bound variable `r`.
  lemma Min_PostStrengthened(s: seq<int>, r: int)
    requires |s| > 0                                          // V1 requires
    requires r in s && forall i | 0 <= i < |s| :: r <= s[i]   // V2 ensures
    ensures r in s                                            // V1 ensures
  {
  }

  // Double — transparent body rewritten: extensional equivalence.
  lemma Double_BodyEquivalent(x: int)
    ensures V1.SeqLib.Double(x) == V2.SeqLib.Double(x)
  {
  }

  // Max — added in V2: additions carry no obligation.
}
