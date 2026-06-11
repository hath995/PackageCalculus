// ConcurrentFeatures.dfy — The Concurrent Feature Package Calculus (§5.2.1).
//
// Definition 5.2.1 of the paper: the feature calculus (§4.4) with version
// uniqueness relaxed to version granularity (§4.2) and dependency
// satisfaction witnessed by a parent relation. The composed reduction
// lowers features first (Definition 4.4.4) and then concurrent versions
// (Definition 4.2.3).
//
// Mechanisation notes:
//   - the paper's ρ ⊆ P × P cannot distinguish which dependency of a
//     parent selected a child (the same aliasing as §4.2/§4.7), so we use
//     selection relations keyed by the dependency occurrence: selP for
//     parameterised and selA for additional dependencies, both functional;
//   - Theorem 5.2.3 (completeness of the composition) is proved in
//     lemmas/ConcurrentFeaturesLemmas.dfy, reusing Theorem 4.2.5;
//   - Theorem 5.2.2 (soundness) is FALSE as stated: the feature reduction
//     achieves feature unification through version uniqueness, which
//     granularity relaxes, so a core resolution of the doubly-reduced
//     instance can satisfy one dependency's required features with two
//     different versions of the dependee ("feature drift") — its
//     extraction then violates Definition 5.2.1's closure.
//     tests/Composition.dfy exhibits an executable counterexample.

include "Core.dfy"
include "Concurrent.dfy"
include "Features.dfy"

module ConcurrentFeatures {
  import opened Core
  import opened Concurrent
  import opened Features

  // Selected child versions, per dependency occurrence.
  type ParamSel = set<((Package, FDep), Version)>
  type AddSel = set<(((Package, Feature), FDep), Version)>

  predicate FunctionalP(selP: ParamSel) {
    forall s1, s2 | s1 in selP && s2 in selP && s1.0 == s2.0 :: s1.1 == s2.1
  }

  predicate FunctionalA(selA: AddSel) {
    forall s1, s2 | s1 in selA && s2 in selA && s1.0 == s2.0 :: s1.1 == s2.1
  }

  // Version v satisfies dependency target d in rf: an entry with that
  // exact package carrying at least the required features.
  predicate CFSelected(rf: FRes, d: FDep, v: Version) {
    v in d.versions
    && exists q | q in rf :: q.0 == Package(d.name, v) && d.feats <= q.1
  }

  // Definition 5.2.1(a) for parameterised dependencies: each dependency of
  // each selected package selects exactly one child (selP is functional).
  predicate CFParamClosure(fdeps: FDepRel, rf: FRes, selP: ParamSel) {
    forall pe, e | pe in rf && e in fdeps && e.0 == pe.0 ::
      exists v | v in e.1.versions :: ((e.0, e.1), v) in selP && CFSelected(rf, e.1, v)
  }

  // ... and for additional dependencies of enabled features.
  predicate CFAddClosure(adeps: AddDepRel, rf: FRes, selA: AddSel) {
    forall pe, a | pe in rf && a in adeps && a.0.0 == pe.0 && a.0.1 in pe.1 ::
      exists v | v in a.1.versions :: ((a.0, a.1), v) in selA && CFSelected(rf, a.1, v)
  }

  // Definition 5.2.1(b): version granularity over the selected packages.
  predicate CFGranularity(g: GranFn, rf: FRes) {
    forall e1, e2 | e1 in rf && e2 in rf
      && e1.0.name == e2.0.name && e1.0.version != e2.0.version ::
      g(e1.0.version) != g(e2.0.version)
  }

  // Definition 5.2.1: (rf, selP, selA) ∈ S_γF(D_γF, A, root, g).
  predicate ValidConcFeatResolution(repo: set<Package>, fsupp: SupportRel,
                                    fdeps: FDepRel, adeps: AddDepRel, g: GranFn,
                                    root: Package, rf: FRes,
                                    selP: ParamSel, selA: AddSel) {
    FResInRepo(repo, fsupp, rf)
    && (exists e | e in rf :: e.0 == root)
    && FeatureUnification(rf)
    && CFGranularity(g, rf)
    && FunctionalP(selP)
    && FunctionalA(selA)
    && CFParamClosure(fdeps, rf, selP)
    && CFAddClosure(adeps, rf, selA)
  }

  // Side conditions for the composed reduction (the concurrent reduction's
  // UniqueDepPerName, surfaced at the feature level).
  predicate CFUniqueDeps(fdeps: FDepRel) {
    forall e1, e2 | e1 in fdeps && e2 in fdeps
      && e1.0 == e2.0 && e1.1.name == e2.1.name :: e1.1 == e2.1
  }

  predicate CFUniqueAdds(adeps: AddDepRel) {
    forall a1, a2 | a1 in adeps && a2 in adeps
      && a1.0 == a2.0 && a1.1.name == a2.1.name :: a1.1 == a2.1
  }

  predicate CFAddNotSelf(adeps: AddDepRel) {
    forall a | a in adeps :: a.1.name != a.0.0.name
  }

  predicate CFNonempty(fdeps: FDepRel, adeps: AddDepRel) {
    (forall e | e in fdeps :: e.1.versions != {})
    && (forall a | a in adeps :: a.1.versions != {})
  }

  predicate WfSupp(repo: set<Package>, fsupp: SupportRel) {
    forall s | s in fsupp :: s.0 in repo
  }

  // The composed reduction: features first, then concurrent versions.
  function ConcFeatReduceRepo(repo: set<Package>, fsupp: SupportRel,
                              fdeps: FDepRel, adeps: AddDepRel, g: GranFn): set<Package> {
    ConcReduceRepo(FeatReduceRepo(repo, fsupp), FeatReduceDeps(fsupp, fdeps, adeps), g)
  }

  function ConcFeatReduceDeps(fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                              g: GranFn): DepRel {
    ConcReduceDeps(FeatReduceDeps(fsupp, fdeps, adeps), g)
  }

  // -----------------------------------------------------------------
  // The construction of Theorem 5.2.3: the parent relation over the
  // feature-reduced packages, one pair per edge kind.
  // -----------------------------------------------------------------

  // Base edges ⟨n, f⟩@v → (n, {v}): the base accompanies its feature pkg.
  function CFRhoBase(rf: FRes): ParentRel {
    set e, f | e in rf && f in e.1 ::
      (e.0, Package(FeatureName(e.0.name, f), e.0.version))
  }

  function CFRhoParamPlain(fdeps: FDepRel, selP: ParamSel): ParentRel {
    set e, v | e in fdeps && e.1.feats == {} && v in e.1.versions
      && ((e.0, e.1), v) in selP ::
      (Package(e.1.name, v), e.0)
  }

  function CFRhoParamFeat(fdeps: FDepRel, selP: ParamSel): ParentRel {
    set e, f, v | e in fdeps && f in e.1.feats && v in e.1.versions
      && ((e.0, e.1), v) in selP ::
      (Package(FeatureName(e.1.name, f), v), e.0)
  }

  function CFRhoAddPlain(adeps: AddDepRel, selA: AddSel): ParentRel {
    set a, v | a in adeps && a.1.feats == {} && v in a.1.versions
      && ((a.0, a.1), v) in selA ::
      (Package(a.1.name, v), Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version))
  }

  function CFRhoAddFeat(adeps: AddDepRel, selA: AddSel): ParentRel {
    set a, f, v | a in adeps && f in a.1.feats && v in a.1.versions
      && ((a.0, a.1), v) in selA ::
      (Package(FeatureName(a.1.name, f), v),
       Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version))
  }

  function ConcFeatRho(rf: FRes, selP: ParamSel, selA: AddSel,
                       fdeps: FDepRel, adeps: AddDepRel): ParentRel {
    CFRhoBase(rf) + CFRhoParamPlain(fdeps, selP) + CFRhoParamFeat(fdeps, selP)
    + CFRhoAddPlain(adeps, selA) + CFRhoAddFeat(adeps, selA)
  }

  // -----------------------------------------------------------------
  // The repaired Theorem 5.2.2 (see README.md and FINDINGS.md).
  //
  // Soundness of the composition fails in general: the feature
  // reduction's per-feature edges re-unify on one dependee version only
  // through version uniqueness, which granularity relaxes. Feature
  // coherence states exactly the missing property of a concurrent
  // resolution of the feature-reduced instance: for each dependency, all
  // of its required features select the same dependee version.
  // -----------------------------------------------------------------

  predicate FeatureCoherent(fdeps: FDepRel, adeps: AddDepRel,
                            rg: set<Package>, rho: ParentRel) {
    (forall e, f1, f2, v1, v2 |
       e in fdeps && f1 in e.1.feats && f2 in e.1.feats
       && v1 in e.1.versions && v2 in e.1.versions
       && Selected((e.0, Dep(FeatureName(e.1.name, f1), e.1.versions)), v1, rg, rho)
       && Selected((e.0, Dep(FeatureName(e.1.name, f2), e.1.versions)), v2, rg, rho)
       :: v1 == v2)
    && (forall a, f1, f2, v1, v2 |
       a in adeps && f1 in a.1.feats && f2 in a.1.feats
       && v1 in a.1.versions && v2 in a.1.versions
       && Selected((Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                    Dep(FeatureName(a.1.name, f1), a.1.versions)), v1, rg, rho)
       && Selected((Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                    Dep(FeatureName(a.1.name, f2), a.1.versions)), v2, rg, rho)
       :: v1 == v2)
  }

  // The selection relations read off a concurrent resolution of the
  // feature-reduced instance (the repaired theorem's witnesses).
  function CFExtractSelP(fdeps: FDepRel, rg: set<Package>, rho: ParentRel): ParamSel {
    (set e, v | e in fdeps && e.1.feats == {} && v in e.1.versions
       && Selected((e.0, Dep(e.1.name, e.1.versions)), v, rg, rho)
       :: ((e.0, e.1), v))
    + (set e, f, v | e in fdeps && f in e.1.feats && v in e.1.versions
       && Selected((e.0, Dep(FeatureName(e.1.name, f), e.1.versions)), v, rg, rho)
       :: ((e.0, e.1), v))
  }

  function CFExtractSelA(adeps: AddDepRel, rg: set<Package>, rho: ParentRel): AddSel {
    (set a, v | a in adeps && a.1.feats == {} && v in a.1.versions
       && Selected((Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                    Dep(a.1.name, a.1.versions)), v, rg, rho)
       :: ((a.0, a.1), v))
    + (set a, f, v | a in adeps && f in a.1.feats && v in a.1.versions
       && Selected((Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                    Dep(FeatureName(a.1.name, f), a.1.versions)), v, rg, rho)
       :: ((a.0, a.1), v))
  }
}
