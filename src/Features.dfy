// Features.dfy — The Feature Package Calculus (§4.4).
//
// Definitions 4.4.1–4.4.4 of the paper, modelling Cargo features, Python
// extras, and Portage USE flags. Packages support features (FS); a
// parameterised dependency (p, (m, S, F)) requires the dependee to be
// selected with at least the features F; an additional dependency
// ((p, f), (m, S, F)) applies only when p is selected with feature f
// enabled. The resolver unifies features: each selected package has one
// feature set, the union of everything requested of it.
//
// The reduction creates a feature package ⟨n, f⟩ per supported feature,
// pinned to its base package's exact version, so that requiring features
// is requiring feature packages, and version uniqueness keeps base and
// feature packages aligned.
//
// Theorems 4.4.5 and 4.4.6 are proved in lemmas/FeaturesLemmas.dfy.

include "Core.dfy"

module Features {
  import opened Core

  type Feature = string

  // Definition 4.4.1(b): FS ⊆ P × F — package p supports feature f.
  type SupportRel = set<(Package, Feature)>

  // Definition 4.4.2(a): parameterised dependencies D_F ⊆ P × (N × ℘(V) × ℘(F)).
  datatype FDep = FDep(name: Name, versions: set<Version>, feats: set<Feature>)
  type FDepRel = set<(Package, FDep)>

  // Definition 4.4.2(b): additional dependencies A ⊆ (P × F) × (N × ℘(V) × ℘(F)).
  type AddDepRel = set<((Package, Feature), FDep)>

  // A feature resolution selects packages together with feature sets.
  type FRes = set<(Package, set<Feature>)>

  // A dependency is satisfied by an entry with a compatible version whose
  // selected features include the required ones.
  predicate FDepSatisfied(rf: FRes, d: FDep) {
    exists q | q in rf ::
      q.0.name == d.name && q.0.version in d.versions && d.feats <= q.1
  }

  // Definition 4.4.3(b).
  predicate ParamClosure(fdeps: FDepRel, rf: FRes) {
    forall pe, e | pe in rf && e in fdeps && e.0 == pe.0 :: FDepSatisfied(rf, e.1)
  }

  // Definition 4.4.3(c).
  predicate AddClosure(adeps: AddDepRel, rf: FRes) {
    forall pe, a | pe in rf && a in adeps && a.0.0 == pe.0 && a.0.1 in pe.1 ::
      FDepSatisfied(rf, a.1)
  }

  // Definition 4.4.3(d): one feature set per selected package.
  predicate FeatureUnification(rf: FRes) {
    forall e1, e2 | e1 in rf && e2 in rf && e1.0 == e2.0 :: e1.1 == e2.1
  }

  // Definition 4.4.3(e).
  predicate FVersionUniqueness(rf: FRes) {
    forall e1, e2 | e1 in rf && e2 in rf && e1.0.name == e2.0.name ::
      e1.0.version == e2.0.version
  }

  // Entries are drawn from existing packages with supported features.
  predicate FResInRepo(repo: set<Package>, fsupp: SupportRel, rf: FRes) {
    forall e | e in rf ::
      e.0 in repo && forall f | f in e.1 :: (e.0, f) in fsupp
  }

  // Definition 4.4.3: rf ∈ S_F(D_F, A, root).
  predicate ValidFeatureResolution(repo: set<Package>, fsupp: SupportRel,
                                   fdeps: FDepRel, adeps: AddDepRel,
                                   root: Package, rf: FRes) {
    FResInRepo(repo, fsupp, rf)
    && (exists e | e in rf :: e.0 == root)
    && ParamClosure(fdeps, rf)
    && AddClosure(adeps, rf)
    && FeatureUnification(rf)
    && FVersionUniqueness(rf)
  }

  // Well-formedness (Definition 4.4.2(a), including its closing remark):
  // referenced packages exist and requested features are supported.
  predicate WfFDeps(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel) {
    forall e | e in fdeps ::
      e.0 in repo
      && forall u | u in e.1.versions ::
           Package(e.1.name, u) in repo
           && forall f | f in e.1.feats :: (Package(e.1.name, u), f) in fsupp
  }

  predicate WfAddDeps(repo: set<Package>, fsupp: SupportRel, adeps: AddDepRel) {
    forall a | a in adeps ::
      a.0.0 in repo
      && forall u | u in a.1.versions ::
           Package(a.1.name, u) in repo
           && forall f | f in a.1.feats :: (Package(a.1.name, u), f) in fsupp
  }

  // Freshness: the instance mentions no synthetic feature packages.
  predicate PlainFeatureInstance(repo: set<Package>, fsupp: SupportRel,
                                 fdeps: FDepRel, adeps: AddDepRel) {
    (forall p | p in repo :: !p.name.FeatureName?)
    && (forall e | e in fdeps :: !e.1.name.FeatureName?)
    && (forall a | a in adeps :: !a.1.name.FeatureName?)
  }

  // ---------------------------------------------------------------------
  // The reduction to the core (Definition 4.4.4).
  // ---------------------------------------------------------------------

  // (a)(ii): one feature package ⟨n, f⟩ at version v per supported feature.
  function FeatPkgs(fsupp: SupportRel): set<Package> {
    set s | s in fsupp :: Package(FeatureName(s.0.name, s.1), s.0.version)
  }

  function FeatReduceRepo(repo: set<Package>, fsupp: SupportRel): set<Package> {
    repo + FeatPkgs(fsupp)
  }

  // (b)(i): each feature package pins its base package's exact version.
  function FeatBaseEdges(fsupp: SupportRel): DepRel {
    set s | s in fsupp ::
      (Package(FeatureName(s.0.name, s.1), s.0.version), Dep(s.0.name, {s.0.version}))
  }

  // (b)(ii): parameterised dependencies — on the plain name when no
  // features are required, else on each required feature package.
  function FeatParamEdges(fdeps: FDepRel): DepRel {
    (set e | e in fdeps && e.1.feats == {} :: (e.0, Dep(e.1.name, e.1.versions)))
    + (set e, f | e in fdeps && f in e.1.feats ::
        (e.0, Dep(FeatureName(e.1.name, f), e.1.versions)))
  }

  // (b)(iii): additional dependencies originate from the feature package.
  function FeatAddEdges(adeps: AddDepRel): DepRel {
    (set a | a in adeps && a.1.feats == {} ::
       (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version), Dep(a.1.name, a.1.versions)))
    + (set a, f | a in adeps && f in a.1.feats ::
       (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
        Dep(FeatureName(a.1.name, f), a.1.versions)))
  }

  function FeatReduceDeps(fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel): DepRel {
    FeatBaseEdges(fsupp) + FeatParamEdges(fdeps) + FeatAddEdges(adeps)
  }

  // ---------------------------------------------------------------------
  // The constructions of Theorems 4.4.5 and 4.4.6.
  // ---------------------------------------------------------------------

  // Theorem 4.4.5: the features selected for p — those whose feature
  // packages accompany p at its version.
  function FeatSelOf(r: set<Package>, p: Package): set<Feature> {
    set q | q in r && q.name.FeatureName?
         && q.name.fbase == p.name && q.version == p.version :: q.name.feat
  }

  // Theorem 4.4.5: each plain package in the core resolution is selected
  // with its accompanying features.
  function FeatExtract(r: set<Package>): FRes {
    set p | p in r && !p.name.FeatureName? :: (p, FeatSelOf(r, p))
  }

  // Theorem 4.4.6: the base packages plus a feature package per selected
  // feature.
  function FeatBuildCore(rf: FRes): set<Package> {
    (set e | e in rf :: e.0)
    + (set e, f | e in rf && f in e.1 :: Package(FeatureName(e.0.name, f), e.0.version))
  }
}
