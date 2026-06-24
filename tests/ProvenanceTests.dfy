// ProvenanceTests.dfy — a worked example of the import-set compatibility model
// (src/Provenance.dfy). Run with `dafny test`.
//
// A four-release library with objects A, B, C:
//   v0: A, B born
//   v1: B breaks            (A unchanged)
//   v2: C born              (A, B unchanged)
//   v3: A breaks            (B, C unchanged)
// The coarse compatibility class bumps at v1, v2, v3 (something broke each
// time). But a consumer that imports only {B} is unaffected by the C-addition
// and the A-break, so its window spans v1..v3 — across those majors — exactly
// the cross-major compatibility the per-import model recovers.

include "../src/Provenance.dfy"
include "../lemmas/ProvenanceLemmas.dfy"

module ProvenanceTests {
  import opened Provenance
  import opened ProvenanceLemmas

  const H := History([
    Release({"A", "B"}, {"A", "B"}),
    Release({"A", "B"}, {"B"}),
    Release({"A", "B", "C"}, {"C"}),
    Release({"A", "B", "C"}, {"A"})
  ])

  method {:test} TestImportWindows() {
    assert WfHistory(H);
    assert Latest(H) == 3;

    // import {B}: B last broke at v1, so MinSupport = 1 and B is compatible
    // across v1, v2, v3 — floating across the C-addition and A-break majors.
    assert ImportsPresentAtLatest(H, {"B"});
    expect MinSupport(H, {"B"}) == 1;
    expect InWindow(H, {"B"}, 1);
    expect InWindow(H, {"B"}, 2);
    expect InWindow(H, {"B"}, 3);
    expect !InWindow(H, {"B"}, 0);   // before B's current form began

    // import {A}: A just broke at v3, so it is pinned to the latest.
    assert ImportsPresentAtLatest(H, {"A"});
    expect MinSupport(H, {"A"}) == 3;
    expect !InWindow(H, {"A"}, 2);

    // import {C}: born at v2.
    assert ImportsPresentAtLatest(H, {"C"});
    expect MinSupport(H, {"C"}) == 2;

    // {B, C} together: bounded by the later of the two (C at v2).
    assert ImportsPresentAtLatest(H, {"B", "C"});
    expect MinSupport(H, {"B", "C"}) == 2;

    // the class window = the full object set {A, B, C}: narrowest of all,
    // pinned to v3 because *something* (A) broke there.
    assert ImportsPresentAtLatest(H, {"A", "B", "C"});
    expect MinSupport(H, {"A", "B", "C"}) == 3;

    print "import {B} window = [1, 3]; class window = [3, 3]\n";
  }

  // ---- combining dependers: the join satisfiability check -----------------
  //
  // Library B exports W, X, Y, Z over three releases. Depender A is authored
  // against the latest form of X, Y (era 2); depender C against the original
  // form of W, Z (era 0). Whether one version of B satisfies both turns ENTIRELY
  // on whether W, Z broke again at v2 — the union of symbols is identical below.

  // Scenario 1 — at v2 EVERYTHING re-breaks. No version shows W,Z in era 0 and
  // X,Y in era 2 at once: the genuine cross-depender conflict, now unsatisfiable.
  const Hconflict := History([
    Release({"W", "X", "Y", "Z"}, {"W", "X", "Y", "Z"}),  // v0: all born
    Release({"W", "X", "Y", "Z"}, {}),                    // v1: stable
    Release({"W", "X", "Y", "Z"}, {"W", "X", "Y", "Z"})   // v2: all re-break
  ])

  // Scenario 2 — at v2 only X,Y break; W,Z keep their original form. Now B@v2
  // satisfies everyone: C's W,Z are still in era 0 at v2.
  const Hcompat := History([
    Release({"W", "X", "Y", "Z"}, {"W", "X", "Y", "Z"}),  // v0: all born
    Release({"W", "X", "Y", "Z"}, {}),                    // v1: stable
    Release({"W", "X", "Y", "Z"}, {"X", "Y"})             // v2: only X,Y break
  ])

  // A needs X,Y in their v2 era; C needs W,Z in their era-0 form. Same union of
  // requirements in both scenarios — only the history differs.
  const U: set<EraReq> := {("X", 2), ("Y", 2), ("W", 0), ("Z", 0)}

  method {:test} TestCombineConflict() {
    assert WfHistory(Hconflict);
    assert ValidVersion(Hconflict, 0) && ValidVersion(Hconflict, 1) && ValidVersion(Hconflict, 2);
    assert WfReq(Hconflict, U);

    // The join is 2 (max required era) — but W is in era 2 there, not era 0.
    expect Join(Hconflict, U) == 2;
    expect !ResolvesAt(Hconflict, U, 2);
    expect !CombinedSatisfiable(Hconflict, U);
    // ...and no earlier version resolves it either: failure at the join is
    // failure everywhere (X,Y are not yet in era 2 below v2).
    expect !ResolvesAt(Hconflict, U, 0);
    expect !ResolvesAt(Hconflict, U, 1);

    print "combine (all re-break at v2): UNSAT — no B version satisfies A and C\n";
  }

  method {:test} TestCombineSat() {
    assert WfHistory(Hcompat);
    assert ValidVersion(Hcompat, 2);
    assert WfReq(Hcompat, U);

    expect Join(Hcompat, U) == 2;
    expect CombinedSatisfiable(Hcompat, U);
    expect ResolvesAt(Hcompat, U, 2);     // the join is the resolution

    print "combine (W,Z stable at v2): SAT at B@v2\n";
  }

  // ---- the same scenarios driven through the dependency-set layer ---------
  //
  // The two dependers as records: A authored against B@v2 importing {X,Y}, C
  // against B@v1 importing {W,Z}. UnionReq derives exactly the hand-written
  // requirement union U above, so the graph layer reproduces the SAT/UNSAT split.

  const DepA := Depender(2, {"X", "Y"})
  const DepC := Depender(1, {"W", "Z"})
  const DS := {DepA, DepC}

  method {:test} TestGraphConflict() {
    assert WfHistory(Hconflict);
    assert ValidVersion(Hconflict, 1) && ValidVersion(Hconflict, 2);
    assert WfDependers(Hconflict, DS);
    GraphResolves(Hconflict, DS);            // ensures WfReq(.., UnionReq(..))

    var Ureq := UnionReq(Hconflict, DS);
    expect Ureq == U;                        // derived union = hand-written union
    expect !CombinedSatisfiable(Hconflict, Ureq);

    print "graph (A@v2{X,Y}, C@v1{W,Z}) over re-break history: UNSAT\n";
  }

  method {:test} TestGraphSat() {
    assert WfHistory(Hcompat);
    assert ValidVersion(Hcompat, 1) && ValidVersion(Hcompat, 2);
    assert WfDependers(Hcompat, DS);
    GraphResolves(Hcompat, DS);

    var Ureq := UnionReq(Hcompat, DS);
    expect Ureq == U;
    expect CombinedSatisfiable(Hcompat, Ureq);
    expect ResolvesAt(Hcompat, Ureq, 2);

    // The payoff: at the resolving version B@v2, depender C still sees W and Z
    // in the very form they had at its anchor B@v1.
    DependerSatisfiedAtJoin(Hcompat, DS, DepC, 2);
    assert SameForm(Hcompat, "W", 1, 2) && SameForm(Hcompat, "Z", 1, 2);

    print "graph (A@v2{X,Y}, C@v1{W,Z}) over W,Z-stable history: SAT at B@v2\n";
  }
}
