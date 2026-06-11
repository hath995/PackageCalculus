// MinVersionTests.dfy — Executable examples for §3.3, run with `dafny test`.
//
//   TestMvsBasic           — minimum-bound resolution by the canonical
//                            greedy (least visited set + per-name maxima).
//   TestStaleBounds        — determinism vs minimality: the canonical MVS
//                            answer keeps bounds contributed by superseded
//                            versions, so a strictly smaller valid
//                            resolution can exist.
//   TestRootSelfUpgradeUnsat — the fresh-root hypothesis is necessary:
//                            a dependency chain demanding the root's own
//                            name at a higher version makes the instance
//                            unsatisfiable, so no greedy can succeed.
//   TestMultiResolve       — uniqueness-free resolution by graph traversal
//                            (Figure 3's diamond), and its reading as the
//                            Concurrent calculus at identity granularity.

include "../src/Core.dfy"
include "../src/Solver.dfy"
include "../src/MinVersion.dfy"
include "../src/Concurrent.dfy"

module MinVersionTests {
  import opened Core
  import opened Solver
  import opened MinVersion
  import opened Concurrent

  function P(s: string, v: Version): Package {
    Package(Atom(s), v)
  }

  method {:test} TestMvsBasic() {
    var root := P("root", 1);
    var b1, b2 := P("b", 1), P("b", 2);
    var c1, c2, c3 := P("c", 1), P("c", 2), P("c", 3);
    var repo := {root, b1, b2, c1, c2, c3};
    var mdeps: MinDepRel := {
      (root, MinDep(Atom("b"), 1)),
      (b1, MinDep(Atom("c"), 2))
    };
    var visited := MvsVisited(repo, mdeps, root);
    var r := MvsOf(visited);
    expect r == {root, b1, c2};
    expect ValidMinResolution(repo, mdeps, root, r);
  }

  // root needs n, m, q at ≥1; n@1 needs m ≥ 5; q@1 needs n ≥ 2 (and n@2
  // drops the m bound). The canonical answer keeps n@1's stale bound,
  // selecting m@5 — deterministic, but {root, n2, m1, q1} is also valid
  // and strictly fresher than necessary is avoided there.
  method {:test} TestStaleBounds() {
    var root := P("root", 1);
    var n1, n2 := P("n", 1), P("n", 2);
    var m1, m5 := P("m", 1), P("m", 5);
    var q1 := P("q", 1);
    var repo := {root, n1, n2, m1, m5, q1};
    var mdeps: MinDepRel := {
      (root, MinDep(Atom("n"), 1)),
      (root, MinDep(Atom("m"), 1)),
      (root, MinDep(Atom("q"), 1)),
      (n1, MinDep(Atom("m"), 5)),
      (q1, MinDep(Atom("n"), 2))
    };
    var visited := MvsVisited(repo, mdeps, root);
    var r := MvsOf(visited);
    expect r == {root, n2, m5, q1};
    expect ValidMinResolution(repo, mdeps, root, r);
    // A pointwise-smaller valid resolution exists: MVS is deterministic,
    // not minimal, in this calculus.
    expect ValidMinResolution(repo, mdeps, root, {root, n2, m1, q1});
  }

  // a@1 → b ≥ 1; b@1 → a ≥ 2: with root a@1, version uniqueness forbids
  // a@2, so no valid resolution exists at all (checked by exhaustive
  // search over the core reduction of the instance).
  method {:test} TestRootSelfUpgradeUnsat() {
    var a1, a2, b1 := P("a", 1), P("a", 2), P("b", 1);
    var repo := {a1, a2, b1};
    var mdeps: MinDepRel := {
      (a1, MinDep(Atom("b"), 1)),
      (b1, MinDep(Atom("a"), 2))
    };
    var coreDeps := Versions.ReduceVf(repo, MinToVf(mdeps));
    var rs := AllResolutions(repo, coreDeps, a1);
    expect rs == {};
  }

  // Figure 3's diamond, solved by approach (2): both versions of D are
  // taken, and the result is a concurrent resolution at identity
  // granularity with the canonical maximal selection.
  method {:test} TestMultiResolve() {
    var a1, b1, c1 := P("a", 1), P("b", 1), P("c", 1);
    var d1, d3 := P("d", 1), P("d", 3);
    var repo := {a1, b1, c1, d1, d3};
    var deps := {
      (a1, Dep(Atom("b"), {1})), (a1, Dep(Atom("c"), {1})),
      (b1, Dep(Atom("d"), {1})), (c1, Dep(Atom("d"), {3}))
    };
    var r := MultiResolve(repo, deps, a1);
    expect MultiValid(repo, deps, a1, r);
    expect d1 in r && d3 in r;
    var idGran: GranFn := v => v;
    expect ValidConcurrentResolution(repo, deps, idGran, a1, r, MaxSelRho(deps, r));
  }
}
