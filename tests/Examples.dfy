// Examples.dfy — Executable examples from the paper, run with `dafny test`.
//
//   TestFigure1            — Figure 1: the only valid resolution.
//   TestDiamondNoResolution— Figure 3: the diamond dependency problem.
//   TestNoMaximumResolution— §3.2: maximal resolutions with no maximum.
//   TestVersionFormulae    — Definition 3.2.3: formula semantics.
//   TestVfReduction        — Definition 3.2.6 on the Figure 1 instance.
//   TestConflictsFigure2   — Figure 2: conflicts and their reduction.
//   TestOptionalExample483 — Example 4.8.3: optional deps & build graphs.
//   TestSingular           — §4.9: singular dependencies.
//   TestPackageFormulae    — §4.5: opam-style ("lwt" | "async") formulae.
//   TestSatEncoding        — Appendix C: the SAT encoding on Figure 1.
//   TestHardness           — Appendix B: 3-SAT instances as resolution
//                            problems, solved by the exhaustive resolver.

include "../src/Core.dfy"
include "../src/Solver.dfy"
include "../src/Versions.dfy"
include "../src/Conflicts.dfy"
include "../src/PackageFormulae.dfy"
include "../src/Optional.dfy"
include "../src/Singular.dfy"
include "../src/SatEncoding.dfy"
include "../src/Hardness.dfy"

module Tests {
  import opened Core
  import opened Solver
  import opened Versions
  import opened Conflicts
  import opened PackageFormulae
  import opened Optional
  import opened Singular
  import SatEncoding
  import Hardness

  function P(s: string, v: Version): Package {
    Package(Atom(s), v)
  }

  function Dp(s: string, vs: set<Version>): Dep {
    Dep(Atom(s), vs)
  }

  // Figure 1: A1 → B(=1), C(=1); B1 → D(≥1,<<3); C1 → D(≥2).
  // "The only valid resolution ... is {root, (b,1), (c,1), (d,2)}."
  method {:test} TestFigure1() {
    var a1, b1, c1 := P("a", 1), P("b", 1), P("c", 1);
    var d1, d2, d3 := P("d", 1), P("d", 2), P("d", 3);
    var repo := {a1, b1, c1, d1, d2, d3};
    var deps := {
      (a1, Dp("b", {1})), (a1, Dp("c", {1})),
      (b1, Dp("d", {1, 2})), (c1, Dp("d", {2, 3}))
    };
    var rs := AllResolutions(repo, deps, a1);
    expect rs == {{a1, b1, c1, d2}};
  }

  // Figure 3: the diamond dependency problem — B wants D=1, C wants D=3,
  // so no valid resolution exists under version uniqueness.
  method {:test} TestDiamondNoResolution() {
    var a1, b1, c1 := P("a", 1), P("b", 1), P("c", 1);
    var d1, d3 := P("d", 1), P("d", 3);
    var repo := {a1, b1, c1, d1, d3};
    var deps := {
      (a1, Dp("b", {1})), (a1, Dp("c", {1})),
      (b1, Dp("d", {1})), (c1, Dp("d", {3}))
    };
    var rs := AllResolutions(repo, deps, a1);
    expect rs == {};
  }

  // §3.2: a maximum resolution may not exist. Both fresh resolutions
  // {a1,b1,c2} and {a1,b2,c1} are maximal but incomparable.
  method {:test} TestNoMaximumResolution() {
    var a1, b1, b2, c1, c2 := P("a", 1), P("b", 1), P("b", 2), P("c", 1), P("c", 2);
    var repo := {a1, b1, b2, c1, c2};
    var deps := {
      (a1, Dp("b", {1, 2})), (b1, Dp("c", {1, 2})), (b2, Dp("c", {1}))
    };
    var rs := AllResolutions(repo, deps, a1);
    var low, fresh1, fresh2 := {a1, b1, c1}, {a1, b1, c2}, {a1, b2, c1};
    expect rs == {low, fresh1, fresh2};
    // low is below both, and is not maximal.
    expect ResLeq(low, fresh1) && ResLeq(low, fresh2);
    expect !(forall rp | rp in rs :: ResLeq(low, rp) ==> rp == low);
    // fresh1 and fresh2 are incomparable, and both are maximal.
    expect !ResLeq(fresh1, fresh2) && !ResLeq(fresh2, fresh1);
    expect forall rp | rp in rs :: ResLeq(fresh1, rp) ==> rp == fresh1;
    expect forall rp | rp in rs :: ResLeq(fresh2, rp) ==> rp == fresh2;
  }

  // Definition 3.2.3(e): version formula semantics, including the literal
  // ⟦= v⟧ = {v} (not intersected with the existing versions).
  method {:test} TestVersionFormulae() {
    var u: set<Version> := {1, 2, 3};
    expect Eval(Top, u) == u;
    expect Eval(VAnd(VCmp(Ge, 1), VCmp(Lt, 3)), u) == {1, 2};   // "^1"-style range
    expect Eval(VCmp(VNe, 2), u) == {1, 3};
    expect Eval(VOr(VCmp(VEq, 1), VCmp(Gt, 2)), u) == {1, 3};
    expect Eval(VCmp(VEq, 5), u) == {5};
  }

  // Definition 3.2.6 / Theorem 3.2.7 on the Figure 1 instance, written
  // with version formulae instead of version sets.
  method {:test} TestVfReduction() {
    var a1, b1, c1 := P("a", 1), P("b", 1), P("c", 1);
    var d1, d2, d3 := P("d", 1), P("d", 2), P("d", 3);
    var repo := {a1, b1, c1, d1, d2, d3};
    var vdeps := {
      (a1, VfDep(Atom("b"), VCmp(VEq, 1))),
      (a1, VfDep(Atom("c"), VCmp(VEq, 1))),
      (b1, VfDep(Atom("d"), VAnd(VCmp(Ge, 1), VCmp(Lt, 3)))),
      (c1, VfDep(Atom("d"), VCmp(Ge, 2)))
    };
    var coreDeps := {
      (a1, Dp("b", {1})), (a1, Dp("c", {1})),
      (b1, Dp("d", {1, 2})), (c1, Dp("d", {2, 3}))
    };
    expect ReduceVf(repo, vdeps) == coreDeps;
    expect ValidVfResolution(repo, vdeps, a1, {a1, b1, c1, d2});
    expect !ValidVfResolution(repo, vdeps, a1, {a1, b1, c1, d1});
  }

  // Figure 2: A1 conflicts with B (<< 3). In the reduced core instance the
  // synthetic kappa package makes the two sides mutually exclusive.
  method {:test} TestConflictsFigure2() {
    var a1, b1, b2 := P("a", 1), P("b", 1), P("b", 2);
    var repo := {a1, b1, b2};
    var deps: DepRel := {};
    var c := (a1, Dp("b", {1, 2}));
    var confl: ConflictRel := {c};
    expect ValidConflictResolution(repo, deps, confl, a1, {a1});
    expect !ValidConflictResolution(repo, deps, confl, a1, {a1, b1});
    expect !ValidConflictResolution(repo, deps, confl, a1, {a1, b2});
    // The reduced instance has exactly one resolution: {a1, kappa@1}.
    var rs := AllResolutions(ReduceRepo(repo, confl), ReduceDeps(deps, confl), a1);
    var kappa1 := Package(KName(c), 1);
    expect rs == {{a1, kappa1}};
    // Theorem 4.1.4: intersecting with the original repository recovers
    // the conflict-calculus resolution.
    expect {a1, kappa1} * repo == {a1};
    // Theorem 4.1.5: the extension of {a1} selects kappa@1.
    expect ExtendWithKappas({a1}, confl) == {a1, kappa1};
  }

  // Example 4.8.3: a →D b, c →D d, d →D a, b →O d. Optional dependencies
  // never pull packages into the resolution; they only order builds when
  // the dependee is present.
  method {:test} TestOptionalExample483() {
    var a1, b1, c1, d1 := P("a", 1), P("b", 1), P("c", 1), P("d", 1);
    var repo := {a1, b1, c1, d1};
    var deps := {(a1, Dp("b", {1})), (c1, Dp("d", {1})), (d1, Dp("a", {1}))};
    var opt: OptRel := {(b1, Dp("d", {1}))};
    // Root a: d is NOT pulled in by the optional dependency.
    expect ValidOptResolution(repo, deps, opt, a1, {a1, b1});
    expect BuildGraphOpt(deps, opt, {a1, b1}) == {(a1, b1)};
    // Root c: d is present, so the optional build edge (b,1) → (d,1) appears.
    var r2 := {c1, d1, a1, b1};
    expect ValidOptResolution(repo, deps, opt, c1, r2);
    expect BuildGraphOpt(deps, opt, r2) == {(a1, b1), (c1, d1), (d1, a1), (b1, d1)};
  }

  // §4.9: singular dependencies pin an exact package.
  method {:test} TestSingular() {
    var a1, b2 := P("a", 1), P("b", 2);
    var repo := {a1, b2};
    var sdeps: SingularRel := {(a1, b2)};
    expect ValidSingularResolution(repo, sdeps, a1, {a1, b2});
    expect !ValidSingularResolution(repo, sdeps, a1, {a1});
    expect SingularToCore(sdeps) == {(a1, Dp("b", {2}))};
    expect ValidResolution(repo, SingularToCore(sdeps), a1, {a1, b2});
  }

  // §4.5: opam's ("lwt" | "async"), and negation acting as a conflict.
  method {:test} TestPackageFormulae() {
    var a1, lwt1, async1 := P("a", 1), P("lwt", 1), P("async", 1);
    var repo := {a1, lwt1, async1};
    var pfdeps: PfDepRel := {(a1, POr(PAtom(Atom("lwt"), {1}), PAtom(Atom("async"), {1})))};
    expect ValidPfResolution(repo, pfdeps, a1, {a1, lwt1});
    expect ValidPfResolution(repo, pfdeps, a1, {a1, async1});
    expect !ValidPfResolution(repo, pfdeps, a1, {a1});
    var b1 := P("b", 1);
    var nf: PfDepRel := {(a1, PNot(PAtom(Atom("b"), {1})))};
    expect ValidPfResolution({a1, b1}, nf, a1, {a1});
    expect !ValidPfResolution({a1, b1}, nf, a1, {a1, b1});
  }

  // Appendix C: the SAT encoding of the Figure 1 instance.
  method {:test} TestSatEncoding() {
    var a1, b1, c1 := P("a", 1), P("b", 1), P("c", 1);
    var d1, d2, d3 := P("d", 1), P("d", 2), P("d", 3);
    var repo := {a1, b1, c1, d1, d2, d3};
    var deps := {
      (a1, Dp("b", {1})), (a1, Dp("c", {1})),
      (b1, Dp("d", {1, 2})), (c1, Dp("d", {2, 3}))
    };
    var cnf := SatEncoding.Encode(repo, deps, a1);
    expect SatEncoding.SatCnf({a1, b1, c1, d2}, cnf);     // Theorem C.3
    expect !SatEncoding.SatCnf({a1, b1, c1, d1}, cnf);    // c's clause fails
    expect !SatEncoding.SatCnf({a1, b1, c1, d1, d2}, cnf);// uniqueness fails
    expect !SatEncoding.SatCnf({}, cnf);                  // root clause fails
  }

  // Appendix B: 3-SAT as dependency resolution.
  method {:test} TestHardness() {
    // (x0 ∨ x1 ∨ x1) ∧ (¬x0 ∨ ¬x0 ∨ ¬x1): satisfiable.
    var f: Hardness.Formula3 := [
      Hardness.Clause3(Hardness.Lit(0, true), Hardness.Lit(1, true), Hardness.Lit(1, true)),
      Hardness.Clause3(Hardness.Lit(0, false), Hardness.Lit(0, false), Hardness.Lit(1, false))
    ];
    assert Hardness.WfFormula(f, 2);
    var rs := AllResolutions(Hardness.EncRepo(f, 2), Hardness.EncDeps(f, 2), Hardness.EncRoot());
    expect rs != {};
    var r :| r in rs;
    var asg := Hardness.ExtractAsg(r, 2);
    expect Hardness.Sat3(asg, f);

    // (x0) ∧ (¬x0): unsatisfiable, so no resolution exists.
    var g: Hardness.Formula3 := [
      Hardness.Clause3(Hardness.Lit(0, true), Hardness.Lit(0, true), Hardness.Lit(0, true)),
      Hardness.Clause3(Hardness.Lit(0, false), Hardness.Lit(0, false), Hardness.Lit(0, false))
    ];
    var rs2 := AllResolutions(Hardness.EncRepo(g, 1), Hardness.EncDeps(g, 1), Hardness.EncRoot());
    expect rs2 == {};
  }
}
