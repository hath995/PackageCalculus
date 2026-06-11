// Extensions.dfy — Executable examples for §4.2, §4.3, §4.4, and §4.7,
// run with `dafny test`.
//
//   TestConcurrentDiamond  — Figure 3's diamond becomes solvable once
//                            multiple versions may coexist.
//   TestConcurrentFigure4  — Figure 4/5: the Cargo-style instance and its
//                            reduction, solved by the exhaustive resolver.
//   TestPeerFigure6        — Figure 6: a peer dependency intersects the
//                            parent's constraint (only C@2 survives).
//   TestFeaturesFigure7    — Figure 7/8: Cargo features with additional
//                            dependencies, and the reduction round trip.
//   TestVirtualFigureD2    — Figure D.2: a virtual package provided by two
//                            packages; exactly one provider is selected.

include "../src/Core.dfy"
include "../src/Solver.dfy"
include "../src/Concurrent.dfy"
include "../src/Peers.dfy"
include "../src/Features.dfy"
include "../src/Virtual.dfy"
include "../src/PackageFormulae.dfy"
include "../src/VariableFormulae.dfy"

module ExtensionTests {
  import opened Core
  import opened Solver
  import opened Concurrent
  import opened Peers
  import opened Features
  import opened Virtual
  import opened PackageFormulae
  import opened VariableFormulae

  function P(s: string, v: Version): Package {
    Package(Atom(s), v)
  }

  function Dp(s: string, vs: set<Version>): Dep {
    Dep(Atom(s), vs)
  }

  // Figure 3's diamond (B wants D=1, C wants D=3) has no core resolution,
  // but with npm/Nix-style granularity (g = identity) both versions of D
  // coexist, each child witnessed by the parent relation.
  method {:test} TestConcurrentDiamond() {
    var a1, b1, c1, d1, d3 := P("a", 1), P("b", 1), P("c", 1), P("d", 1), P("d", 3);
    var repo := {a1, b1, c1, d1, d3};
    var deps := {
      (a1, Dp("b", {1})), (a1, Dp("c", {1})),
      (b1, Dp("d", {1})), (c1, Dp("d", {3}))
    };
    var idGran: GranFn := v => v;
    var r := {a1, b1, c1, d1, d3};
    var rho: ParentRel := {(b1, a1), (c1, a1), (d1, b1), (d3, c1)};
    expect ValidConcurrentResolution(repo, deps, idGran, a1, r, rho);
    // With the constant granularity (the core's single-version behaviour,
    // Definition 4.2.1) the same selection is rejected.
    var oneGran: GranFn := v => 0;
    expect !ValidConcurrentResolution(repo, deps, oneGran, a1, r, rho);
  }

  // Figure 4: A → B(=1.0.0), C(=1.0.0); B → D(">=1, <3"); C → D(">=2, <4"),
  // with Cargo's granularity g(major.minor.patch) = major. Versions are
  // encoded as major*100 + minor*10 + patch.
  method {:test} TestConcurrentFigure4() {
    var a, b, c := P("a", 100), P("b", 100), P("c", 100);
    var d100, d200, d201, d300 := P("d", 100), P("d", 200), P("d", 201), P("d", 300);
    var repo := {a, b, c, d100, d200, d201, d300};
    var depB := (b, Dp("d", {100, 200, 201}));
    var depC := (c, Dp("d", {200, 201, 300}));
    var deps := {(a, Dp("b", {100})), (a, Dp("c", {100})), depB, depC};
    var major: GranFn := v => v / 100;

    var rs := AllResolutions(ConcReduceRepo(repo, deps, major),
                             ConcReduceDeps(deps, major), GPkg(a, major));
    expect rs != {};

    // The two-major-versions selection of Figure 4(c): B takes D 1.0.0 and
    // C takes D 3.0.0, via the split intermediates.
    var twoMajors := {
      GPkg(a, major), GPkg(b, major), GPkg(c, major),
      Package(IName(depB), 1), Package(IName(depC), 3),
      GPkg(d100, major), GPkg(d300, major)
    };
    expect twoMajors in rs;

    // Theorem 4.2.4 executed: every reduced resolution extracts to a valid
    // concurrent resolution.
    var r :| r in rs;
    expect ValidConcurrentResolution(repo, deps, major, a,
                                     ConcExtractRes(r, major),
                                     ConcExtractRho(r, deps, major));
  }

  // Figure 6: parent A depends on child B (which has a peer dependency on
  // C with versions {1,2}) and on C with versions {2,3}. The resolved C
  // must satisfy both constraints: only C@2 works.
  method {:test} TestPeerFigure6() {
    var a1, b1 := P("a", 1), P("b", 1);
    var c1, c2, c3 := P("c", 1), P("c", 2), P("c", 3);
    var repo := {a1, b1, c1, c2, c3};
    var depB := (a1, Dp("b", {1}));
    var depC := (a1, Dp("c", {2, 3}));
    var deps := {depB, depC};
    var peers: PeerRel := {(b1, Dp("c", {1, 2}))};
    var idGran: GranFn := v => v;

    // Semantically: C@2 satisfies both, C@3 only the parent.
    var rho2: ParentRel := {(b1, a1), (c2, a1)};
    expect ValidPeerResolution(repo, deps, peers, idGran, a1, {a1, b1, c2}, rho2);
    var rho3: ParentRel := {(b1, a1), (c3, a1)};
    expect ValidConcurrentResolution(repo, deps, idGran, a1, {a1, b1, c3}, rho3);
    expect !ValidPeerResolution(repo, deps, peers, idGran, a1, {a1, b1, c3}, rho3);

    // In the reduced instance the peer edge forbids the intermediate for C
    // from ever sitting at version 3.
    var rs := AllResolutions(PeerReduceRepo(repo, deps, peers, idGran),
                             PeerReduceDeps(deps, peers, idGran), GPkg(a1, idGran));
    expect rs != {};
    expect forall r | r in rs :: Package(IName(depC), 3) !in r;
    expect exists r | r in rs :: Package(IName(depC), 2) in r;
  }

  // Figure 7: B depends on D{1} with features {alpha, beta}; C on D{1}
  // with {beta}; D's alpha adds a dependency on E, beta on F. Feature
  // unification selects D with {alpha, beta}, pulling in both E and F.
  method {:test} TestFeaturesFigure7() {
    var a1, b1, c1, d1, e1, f1 := P("a", 1), P("b", 1), P("c", 1), P("d", 1), P("e", 1), P("f", 1);
    var repo := {a1, b1, c1, d1, e1, f1};
    var fsupp: SupportRel := {(d1, "alpha"), (d1, "beta")};
    var fdeps: FDepRel := {
      (a1, FDep(Atom("b"), {1}, {})),
      (a1, FDep(Atom("c"), {1}, {})),
      (b1, FDep(Atom("d"), {1}, {"alpha", "beta"})),
      (c1, FDep(Atom("d"), {1}, {"beta"}))
    };
    var adeps: AddDepRel := {
      ((d1, "alpha"), FDep(Atom("e"), {1}, {})),
      ((d1, "beta"), FDep(Atom("f"), {1}, {}))
    };

    var rf: FRes := {
      (a1, {}), (b1, {}), (c1, {}), (d1, {"alpha", "beta"}), (e1, {}), (f1, {})
    };
    expect ValidFeatureResolution(repo, fsupp, fdeps, adeps, a1, rf);
    // Dropping E breaks alpha's additional dependency.
    var rfNoE: FRes := {(a1, {}), (b1, {}), (c1, {}), (d1, {"alpha", "beta"}), (f1, {})};
    expect !ValidFeatureResolution(repo, fsupp, fdeps, adeps, a1, rfNoE);

    // Reduction round trip (Theorems 4.4.5/4.4.6 executed): the built core
    // resolution is found by the exhaustive resolver and extracts back.
    var rs := AllResolutions(FeatReduceRepo(repo, fsupp),
                             FeatReduceDeps(fsupp, fdeps, adeps), a1);
    var r0 := FeatBuildCore(rf);
    expect r0 in rs;
    expect FeatExtract(r0) == rf;
  }

  // Figure D.2: A depends on the virtual package V, provided by both B and
  // C. A valid resolution selects exactly one provider.
  method {:test} TestVirtualFigureD2() {
    var a1, b1, c1 := P("a", 1), P("b", 1), P("c", 1);
    var repo := {a1, b1, c1};
    var depV := (a1, Dp("v", {1}));
    var deps := {depV};
    var prov: ProvidesRel := {(b1, (Atom("v"), Wild)), (c1, (Atom("v"), Wild))};

    // Semantically: one provider is valid, two are not, none is not.
    expect ValidVirtualResolution(repo, deps, prov, a1, {a1, b1},
                                  {((a1, Atom("v")), b1)});
    expect ValidVirtualResolution(repo, deps, prov, a1, {a1, c1},
                                  {((a1, Atom("v")), c1)});
    expect !ValidVirtualResolution(repo, deps, prov, a1, {a1}, {});
    expect !ValidVirtualResolution(repo, deps, prov, a1, {a1, b1, c1},
                                   {((a1, Atom("v")), b1), ((a1, Atom("v")), c1)});

    // The reduction: the intermediate ⟨A, v⟩'s version selects the provider.
    var enc: EncFn := p => if p == b1 then 1 else if p == c1 then 2 else 0;
    var rs := AllResolutions(VirtReduceRepo(repo, deps, prov, enc),
                             VirtReduceDeps(repo, deps, prov, enc), a1);
    expect {a1, Package(PName(depV), 1), b1} in rs;
    expect {a1, Package(PName(depV), 2), c1} in rs;
    // No resolution selects B's intermediate without B itself.
    expect forall r | r in rs ::
      Package(PName(depV), 1) in r ==> b1 in r;
  }

  // Figure D.1: Portage's A-1 with
  //   DEPEND="|| ( ( =B-2 =C-1 ) ( =B-1 !!C ) )"
  // i.e. ψ = ((B,{2}) ∧ (C,{1})) ∨ ((B,{1}) ∧ ¬(C,{1})), reduced to the
  // core via a Tseitin disjunction package and a negated-atom conflict
  // package. The exhaustive resolver confirms the reduction is exact on
  // this instance: its two core resolutions project onto exactly the two
  // formula-calculus resolutions.
  method {:test} TestPackageFormulaReduction() {
    var a1, b1, b2, c1 := P("a", 1), P("b", 1), P("b", 2), P("c", 1);
    var repo := {a1, b1, b2, c1};
    var d1 := PAnd(PAtom(Atom("b"), {2}), PAtom(Atom("c"), {1}));
    var d2 := PAnd(PAtom(Atom("b"), {1}), PNot(PAtom(Atom("c"), {1})));
    var psi := POr(d1, d2);
    var pfdeps: PfDepRel := {(a1, psi)};

    // Formula-calculus resolutions (Definition 4.5.3).
    expect ValidPfResolution(repo, pfdeps, a1, {a1, b2, c1});
    expect ValidPfResolution(repo, pfdeps, a1, {a1, b1});
    expect !ValidPfResolution(repo, pfdeps, a1, {a1, b1, c1});
    expect !ValidPfResolution(repo, pfdeps, a1, {a1, b2});

    // The reduced core instance (Definition 4.5.4).
    var orn := OrName(d1, d2);
    var nu := NegName(Atom("c"), {1});
    var rs := AllResolutions(PfReduceRepo(repo, pfdeps), PfReduceDeps(pfdeps), a1);
    var viaFirst := {a1, Package(orn, 0), b2, c1, Package(nu, 0)};
    var viaSecond := {a1, Package(orn, 1), b1, Package(nu, 1)};
    expect rs == {viaFirst, viaSecond};
    expect viaFirst * repo == {a1, b2, c1} && viaSecond * repo == {a1, b1};
  }

  // §4.6: opam's depends: [ "foo" { os = "linux" } ], expressed as the
  // variable formula ¬(os = linux) ∨ (foo ∧ os = linux), evaluated under
  // assignments for the global variable os (0 = linux, 1 = windows).
  method {:test} TestVariableFormulae() {
    var a1, foo1 := P("a", 1), P("foo", 1);
    var repo := {a1, foo1};
    var LINUX: VarValue := 0;
    var WINDOWS: VarValue := 1;
    var filtered := VfOr(VfNot(VfGlobal("os", Eq, LINUX)),
                         VfAnd(VfAtom(Atom("foo"), {1}), VfGlobal("os", Eq, LINUX)));
    var vdeps: VFormDepRel := {(a1, filtered)};
    var onLinux: Assignment := map[GlobalVar("os") := LINUX];
    var onWindows: Assignment := map[GlobalVar("os") := WINDOWS];

    // On linux, foo is required; elsewhere the dependency is vacuous.
    expect ValidVarFormResolution(repo, vdeps, a1, {a1, foo1}, onLinux);
    expect !ValidVarFormResolution(repo, vdeps, a1, {a1}, onLinux);
    expect ValidVarFormResolution(repo, vdeps, a1, {a1}, onWindows);

    // A package-local variable (opam's with-test) is resolved against the
    // depender.
    var withTest := VfOr(VfNot(VfLocal("with-test", Eq, 1)), VfAtom(Atom("tst"), {1}));
    var tst1 := P("tst", 1);
    var testsOn: Assignment := map[LocalVar(a1, "with-test") := 1];
    var testsOff: Assignment := map[LocalVar(a1, "with-test") := 0];
    expect ValidVarFormResolution({a1, tst1}, {(a1, withTest)}, a1, {a1, tst1}, testsOn);
    expect !ValidVarFormResolution({a1, tst1}, {(a1, withTest)}, a1, {a1}, testsOn);
    expect ValidVarFormResolution({a1, tst1}, {(a1, withTest)}, a1, {a1}, testsOff);
  }

  // Definition 4.6.3 / Theorems 4.6.4–4.6.5 executed: the os-filtered
  // dependency reduced to the core, under both assignments.
  method {:test} TestVariableFormulaReduction() {
    var a1, foo1 := P("a", 1), P("foo", 1);
    var repo := {a1, foo1};
    var LINUX: VarValue := 0;
    var WINDOWS: VarValue := 1;
    var univ: VarUniverse := {(GlobalVar("os"), LINUX), (GlobalVar("os"), WINDOWS)};
    var filtered := VfOr(VfNot(VfGlobal("os", Eq, LINUX)),
                         VfAnd(VfAtom(Atom("foo"), {1}), VfGlobal("os", Eq, LINUX)));
    var vdeps: VFormDepRel := {(a1, filtered)};
    var onLinux: Assignment := map[GlobalVar("os") := LINUX];
    var onWindows: Assignment := map[GlobalVar("os") := WINDOWS];

    // Theorem 4.6.5's construction yields valid core resolutions of the
    // reduced instance for both platforms.
    var r1 := VarBuildCore({a1, foo1}, onLinux, vdeps, univ);
    expect ValidResolution(VarReduceRepo(repo, vdeps, univ), VarReduceDeps(vdeps, univ), a1, r1);
    var r2 := VarBuildCore({a1}, onWindows, vdeps, univ);
    expect ValidResolution(VarReduceRepo(repo, vdeps, univ), VarReduceDeps(vdeps, univ), a1, r2);

    // Theorem 4.6.4's extraction recovers the resolution and assignment.
    expect r1 * repo == {a1, foo1};
    expect r1 * VarPkgsUniverse(univ) == {Package(GlobalVarName("os"), LINUX)};
    expect r2 * repo == {a1};
  }
}
