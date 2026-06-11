// Composition.dfy — Executable examples for §5.2, run with `dafny test`.
//
//   TestConcFeatFigure9 — Figure 9: the Concurrent Feature Package
//     Calculus instance, validated and pushed through Theorem 5.2.3's
//     construction to a checked core resolution of the doubly-reduced
//     instance.
//
//   TestFeatureDrift — a counterexample to Theorem 5.2.2 as stated: a
//     valid core resolution of the doubly-reduced instance whose
//     extraction (per Theorems 4.2.4 and 4.4.5) splits one dependency's
//     required features {f1, f2} across two versions of the dependee —
//     d@1.0.0 carrying f1 and d@2.0.0 carrying f2 — so no selection can
//     satisfy Definition 5.2.1's closure for that dependency. The feature
//     reduction achieves feature *unification* through version uniqueness,
//     which version granularity deliberately relaxes.

include "../src/Core.dfy"
include "../src/Concurrent.dfy"
include "../src/Features.dfy"
include "../src/ConcurrentFeatures.dfy"

module CompositionTests {
  import opened Core
  import opened Concurrent
  import opened Features
  import opened ConcurrentFeatures

  function P(s: string, v: Version): Package {
    Package(Atom(s), v)
  }

  // Figure 9: B → D(">=1, <3") with feature alpha; C → D(">=2, <4") with
  // feature beta; granularity is the identity, so B can take D@1 {alpha}
  // while C takes D@3 {beta}.
  method {:test} TestConcFeatFigure9() {
    var a1, b1, c1 := P("a", 1), P("b", 1), P("c", 1);
    var d1, d2, d3 := P("d", 1), P("d", 2), P("d", 3);
    var repo := {a1, b1, c1, d1, d2, d3};
    var fsupp: SupportRel := {
      (d1, "alpha"), (d2, "alpha"), (d3, "alpha"),
      (d1, "beta"), (d2, "beta"), (d3, "beta")
    };
    var depB := (a1, FDep(Atom("b"), {1}, {}));
    var depC := (a1, FDep(Atom("c"), {1}, {}));
    var depBD := (b1, FDep(Atom("d"), {1, 2}, {"alpha"}));
    var depCD := (c1, FDep(Atom("d"), {2, 3}, {"beta"}));
    var fdeps: FDepRel := {depB, depC, depBD, depCD};
    var adeps: AddDepRel := {};
    var idGran: GranFn := v => v;

    var rf: FRes := {(a1, {}), (b1, {}), (c1, {}), (d1, {"alpha"}), (d3, {"beta"})};
    var selP: ParamSel := {((a1, depB.1), 1), ((a1, depC.1), 1), ((b1, depBD.1), 1), ((c1, depCD.1), 3)};
    var selA: AddSel := {};
    expect ValidConcFeatResolution(repo, fsupp, fdeps, adeps, idGran, a1, rf, selP, selA);

    // Theorem 5.2.3's construction yields a valid core resolution of the
    // doubly-reduced instance (checked executably).
    var depsF := FeatReduceDeps(fsupp, fdeps, adeps);
    var rho := ConcFeatRho(rf, selP, selA, fdeps, adeps);
    var core := ConcBuildCore(FeatBuildCore(rf), rho, depsF, idGran);
    expect ValidResolution(ConcFeatReduceRepo(repo, fsupp, fdeps, adeps, idGran),
                           ConcFeatReduceDeps(fsupp, fdeps, adeps, idGran),
                           GPkg(a1, idGran), core);

    // The repaired Theorem 5.2.2, round-tripped: this core resolution is
    // feature-coherent, so its extraction is a valid Concurrent Feature
    // resolution again.
    var rgX := ConcExtractRes(core, idGran);
    var rhoX := ConcExtractRho(core, depsF, idGran);
    expect FeatureCoherent(fdeps, adeps, rgX, rhoX);
    expect ValidConcFeatResolution(repo, fsupp, fdeps, adeps, idGran, a1,
                                   FeatExtract(rgX),
                                   CFExtractSelP(fdeps, rgX, rhoX),
                                   CFExtractSelA(adeps, rgX, rhoX));
  }

  // The 5.2.2 counterexample. One dependency requires both features of d:
  //   a → (d, {100, 200}, {f1, f2})       (versions encode 1.0.0, 2.0.0)
  // with Cargo's major-version granularity g(v) = v / 100.
  method {:test} TestFeatureDrift() {
    var a, d100, d200 := P("a", 100), P("d", 100), P("d", 200);
    var repo := {a, d100, d200};
    var fsupp: SupportRel := {(d100, "f1"), (d100, "f2"), (d200, "f1"), (d200, "f2")};
    var theDep := FDep(Atom("d"), {100, 200}, {"f1", "f2"});
    var fdeps: FDepRel := {(a, theDep)};
    var adeps: AddDepRel := {};
    var major: GranFn := v => v / 100;

    var depsF := FeatReduceDeps(fsupp, fdeps, adeps);
    var repoF := FeatReduceRepo(repo, fsupp);

    // A valid core resolution of the doubly-reduced instance in which the
    // f1 edge selects d@100 and the f2 edge selects d@200 — both
    // granular versions of d coexist.
    var fp1 := Package(FeatureName(Atom("d"), "f1"), 100);
    var fp2 := Package(FeatureName(Atom("d"), "f2"), 200);
    var edge1 := (a, Dep(FeatureName(Atom("d"), "f1"), {100, 200}));
    var edge2 := (a, Dep(FeatureName(Atom("d"), "f2"), {100, 200}));
    var rdrift := {
      GPkg(a, major),
      Package(IName(edge1), 1), Package(IName(edge2), 2),
      GPkg(fp1, major), GPkg(fp2, major),
      GPkg(d100, major), GPkg(d200, major)
    };
    expect ValidResolution(ConcFeatReduceRepo(repo, fsupp, fdeps, adeps, major),
                           ConcFeatReduceDeps(fsupp, fdeps, adeps, major),
                           GPkg(a, major), rdrift);

    // Theorem 4.2.4's extraction is concurrent-valid (as proved) ...
    var rg := ConcExtractRes(rdrift, major);
    var rho := ConcExtractRho(rdrift, depsF, major);
    expect ValidConcurrentResolution(repoF, depsF, major, a, rg, rho);

    // ... and Theorem 4.4.5's extraction splits the features: d@100
    // carries f1, d@200 carries f2, and no version carries both.
    var rfX := FeatExtract(rg);
    expect (a, {}) in rfX;
    expect (d100, {"f1"}) in rfX && (d200, {"f2"}) in rfX;
    expect forall v: Version | v in {100, 200} :: !CFSelected(rfX, theDep, v);
    // Hence no selection relations can make the extraction satisfy
    // Definition 5.2.1's closure for a's dependency: Theorem 5.2.2 fails
    // as stated. The drift is exactly a failure of feature coherence —
    // the hypothesis of the repaired theorem.
    expect !FeatureCoherent(fdeps, adeps, rg, rho);
  }
}
