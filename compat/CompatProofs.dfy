// CompatProofs.dfy — the AUTHOR-MAINTAINED file of the compatibility
// checking convention. When the solver cannot discharge a generated
// obligation automatically (typically implications between recursive
// predicates, which need induction), the author proves it here under the
// `<Obligation>_Manual` naming convention; the generator then emits a
// call to the manual lemma as the obligation's body instead of `{}`.
// Regenerating the obligations never clobbers this file.

include "SeqLibV1.dfy"
include "SeqLibV2.dfy"

module CompatProofsV1V2 {
  import V1
  import V2

  // Adjacent-pairs sortedness implies pairwise sortedness — by induction
  // on the distance between the indices.
  lemma SortedRange(s: seq<int>, i: int, j: int)
    requires V1.SeqLib.Sorted(s)
    requires 0 <= i < j < |s|
    ensures s[i] <= s[j]
    decreases j - i
  {
    if i + 1 < j {
      SortedRange(s, i, j - 1);
    }
  }

  // The manual proof for the IndexOf precondition-weakening obligation:
  // V1's (adjacent) Sorted implies V2's (pairwise) Sorted.
  lemma IndexOf_PreWeakened_Manual(s: seq<int>, x: int)
    requires V1.SeqLib.Sorted(s) && x in s
    ensures V2.SeqLib.Sorted(s) && x in s
  {
    forall i, j | 0 <= i < j < |s|
      ensures s[i] <= s[j]
    {
      SortedRange(s, i, j);
    }
  }
}
