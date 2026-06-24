// ProvenanceGraphTests.dfy — a worked transitive resolution (src/ProvenanceGraph.dfy).
// Run with `dafny test`.
//
// Three libraries, app -> util -> core:
//   core: object K. v0 K born, v1 stable, v2 K breaks. Eras [0,1] and [2].
//   util: object U. v0 U born, v1 U breaks. util@0 was authored against core v1
//         (K era 0), util@1 against core v2 (K era 2).
//   app:  object A. v0, authored against util v1 (U era 1).
//
// Picking app@0 forces util@1 (only U in era 1), which forces core@2 (its edge
// wants K era 2) — a transitive propagation. In the conflict variant app ALSO
// imports core directly at era 0, which no single core version can reconcile
// with util@1's demand for era 2.

include "../src/ProvenanceGraph.dfy"
include "../lemmas/ProvenanceGraphLemmas.dfy"
include "../src/GraphSolver.dfy"

module ProvenanceGraphTests {
  import opened Core
  import opened Versions
  import opened Provenance
  import opened ProvenanceGraph
  import opened ProvenanceGraphLemmas
  import opened GraphSolver

  const Hcore := History([
    Release({"K"}, {"K"}),   // v0: K born
    Release({"K"}, {}),      // v1: stable
    Release({"K"}, {"K"})    // v2: K breaks
  ])

  const Hutil := History([
    Release({"U"}, {"U"}),   // v0: U born
    Release({"U"}, {"U"})    // v1: U breaks
  ])

  const Happ := History([
    Release({"A"}, {"A"})    // v0: A born
  ])

  const core := Atom("core")
  const util := Atom("util")
  const app := Atom("app")

  const Hists := map[core := Hcore, util := Hutil, app := Happ]

  // util@0 -> core@v1 (K era 0); util@1 -> core@v2 (K era 2); app@0 -> util@v1.
  const BaseEdges :=
    map[(util, 0) := {Edge(core, 1, {"K"})},
        (util, 1) := {Edge(core, 2, {"K"})},
        (app, 0)  := {Edge(util, 1, {"U"})}]

  const USat := Universe(Hists, BaseEdges)

  method {:test} TestGraphChainResolves() {
    assert WfHistory(Hcore) && WfHistory(Hutil) && WfHistory(Happ);
    assert WfUniverse(USat);

    // app@0 forces util@1 forces core@2 — the transitive pick.
    var sel := map[app := 0, util := 1, core := 2];
    expect ValidGraphResolution(USat, app, sel);

    print "graph chain app->util->core: app@0 => util@1 => core@2  RESOLVES\n";
  }

  method {:test} TestReductionToCore() {
    assert WfHistory(Hcore) && WfHistory(Hutil) && WfHistory(Happ);
    assert WfGraph(USat);

    var sel := map[app := 0, util := 1, core := 2];
    assert ValidGraphResolution(USat, app, sel);

    // Via GraphReducesToCore (= the per-edge formula reduction + Theorem 3.2.7),
    // the same selection is an ordinary CORE resolution over the reduced problem.
    GraphReducesToCore(USat, app, sel);
    assert ValidResolution(Repo(USat), ReduceVf(Repo(USat), ToVfDeps(USat)),
                           Package(app, 0), SelToSet(sel));

    print "reduction: graph resolution = core resolution over reduced deps  OK\n";
  }

  method {:test} TestRunnableResolver() {
    assert WfHistory(Hcore) && WfHistory(Hutil) && WfHistory(Happ);

    // Run the resolver on the SAT chain: it finds the unique resolution.
    assert WfGraph(USat);
    var rs := ResolveGraph(USat, app, 0);
    var want := SelToSet(map[app := 0, util := 1, core := 2]);
    expect want in rs;
    expect |rs| == 1;

    // Run it on the conflict universe: no resolution exists.
    assert WfGraph(UConf);
    var rsConf := ResolveGraph(UConf, app, 0);
    expect rsConf == {};

    print "runnable resolver: USat -> {app@0,util@1,core@2}; UConf -> none\n";
  }

  // Conflict variant: app@0 additionally imports core directly at era 0 (anchor
  // v1), while the util@1 it forces demands core era 2. The two requirements on
  // core are the same object K in two different eras.
  const ConflictEdges :=
    map[(util, 0) := {Edge(core, 1, {"K"})},
        (util, 1) := {Edge(core, 2, {"K"})},
        (app, 0)  := {Edge(util, 1, {"U"}), Edge(core, 1, {"K"})}]

  const UConf := Universe(Hists, ConflictEdges)

  // No selection at all resolves the conflict universe. Any valid resolution
  // must take app@0 (the only app version), which forces util@1 (the only U in
  // era 1), which activates util@1's edge demanding core era 2 — while app@0's
  // own direct edge demands core era 0. GraphClauseOne closes it.
  lemma ConflictUnresolvable(sel: map<Name, Version>)
    requires WfUniverse(UConf)
    requires ValidGraphResolution(UConf, app, sel)
    ensures false
  {
    // app is selected, and Happ has a single version, so sel[app] == 0.
    assert app in sel && ValidVersion(Happ, sel[app]);
    assert sel[app] == 0;

    // app@0's util edge forces util into the selection in U's era-1 form.
    var eU := Edge(util, 1, {"U"});
    assert eU in UConf.edges[(app, 0)];
    assert util in sel && EdgeSatH(Hutil, 1, {"U"}, sel[util]);
    assert LastBreak(Hutil, "U", sel[util]) == LastBreak(Hutil, "U", 1) == 1;
    // U is in era 1 only at util v1.
    if sel[util] == 0 {
      assert LastBreak(Hutil, "U", 0) == 0;   // contradicts era 1
    }
    assert sel[util] == 1;

    // util@1 demands core era 2; app@0 demands core era 0 — same object K.
    var eCoreUtil := Edge(core, 2, {"K"});   // from util@1
    var eCoreApp  := Edge(core, 1, {"K"});   // from app@0
    assert eCoreUtil in UConf.edges[(util, sel[util])];
    assert eCoreApp in UConf.edges[(app, sel[app])];
    assert LastBreak(Hcore, "K", 2) != LastBreak(Hcore, "K", 1);
    GraphClauseOne(UConf, app, sel, util, eCoreUtil, app, eCoreApp, core, "K");
  }

  method {:test} TestGraphChainConflict() {
    assert WfHistory(Hcore) && WfHistory(Hutil) && WfHistory(Happ);
    assert WfUniverse(UConf);

    // Proved, not just sampled: NO selection whatsoever resolves this universe.
    assert forall sel | ValidGraphResolution(UConf, app, sel) :: false by {
      forall sel | ValidGraphResolution(UConf, app, sel) ensures false {
        ConflictUnresolvable(sel);
      }
    }

    // The intended resolution cannot be completed: with app@0 and util@1, no
    // core version works — core@2 fails app's direct (era-0) edge, while core@0
    // and core@1 fail util@1's (era-2) edge.
    expect !ValidGraphResolution(UConf, app, map[app := 0, util := 1, core := 2]);
    expect !ValidGraphResolution(UConf, app, map[app := 0, util := 1, core := 1]);
    expect !ValidGraphResolution(UConf, app, map[app := 0, util := 1, core := 0]);

    // And the conflict IS clause 1 of the single-library layer: core's two
    // in-edge demands collect to {(K,0),(K,2)} — one object, two eras —
    // which is not SingleTagged, hence not CombinedSatisfiable.
    var coreReqs: set<EraReq> := {("K", 0), ("K", 2)};
    expect !SingleTagged(coreReqs);
    assert WfReq(Hcore, coreReqs);
    expect !CombinedSatisfiable(Hcore, coreReqs);

    print "graph chain conflict: core demanded in eras 0 AND 2  UNSATISFIABLE\n";
  }
}
