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

module ProvenanceTests {
  import opened Provenance

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
}
