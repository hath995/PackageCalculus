// ConcurrentFeaturesLemmas.dfy — Proofs for §5.2.1.
//
//   Theorem 5.2.3 (Completeness of the composition): a Concurrent Feature
//     resolution yields, through the feature construction (the "bridge")
//     and Theorem 4.2.5, a valid core resolution of the doubly-reduced
//     instance.
//
//   Theorem 5.2.2 (Soundness) is NOT proved: it fails as stated — see
//     tests/Composition.dfy for an executable counterexample ("feature
//     drift") and README.md for discussion.

include "../src/ConcurrentFeatures.dfy"
include "ConcurrentLemmas.dfy"
include "FeaturesLemmas.dfy"

module ConcurrentFeaturesLemmas {
  import opened Core
  import opened Concurrent
  import opened Features
  import opened ConcurrentFeatures
  import ConcurrentLemmas
  import FeaturesLemmas

  // ---------------------------------------------------------------------
  // The feature-reduced instance meets the concurrent reduction's side
  // conditions.
  // ---------------------------------------------------------------------

  // Every reduced edge has one of five shapes.
  lemma FeatEdgeDecode(fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel, ed: (Package, Dep))
    requires ed in FeatReduceDeps(fsupp, fdeps, adeps)
    ensures (exists s | s in fsupp ::
               ed == (Package(FeatureName(s.0.name, s.1), s.0.version), Dep(s.0.name, {s.0.version})))
         || (exists e | e in fdeps ::
               e.1.feats == {} && ed == (e.0, Dep(e.1.name, e.1.versions)))
         || (exists e, f | e in fdeps && f in e.1.feats ::
               ed == (e.0, Dep(FeatureName(e.1.name, f), e.1.versions)))
         || (exists a | a in adeps ::
               a.1.feats == {} && ed == (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                                         Dep(a.1.name, a.1.versions)))
         || (exists a, f | a in adeps && f in a.1.feats ::
               ed == (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                      Dep(FeatureName(a.1.name, f), a.1.versions)))
  {
  }

  lemma FeatDepsWf(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel)
    requires WfFDeps(repo, fsupp, fdeps)
    requires WfAddDeps(repo, fsupp, adeps)
    requires WfSupp(repo, fsupp)
    requires WfAddOwners(fsupp, adeps)
    ensures WfDeps(FeatReduceRepo(repo, fsupp), FeatReduceDeps(fsupp, fdeps, adeps))
  {
    var repoF := FeatReduceRepo(repo, fsupp);
    forall ed | ed in FeatReduceDeps(fsupp, fdeps, adeps)
      ensures ed.0 in repoF && forall v | v in ed.1.versions :: Package(ed.1.name, v) in repoF
    {
      FeatEdgeDecode(fsupp, fdeps, adeps, ed);
      if s :| (s in fsupp
           && ed == (Package(FeatureName(s.0.name, s.1), s.0.version), Dep(s.0.name, {s.0.version}))) {
        assert ed.0 in FeatPkgs(fsupp);
        assert Package(s.0.name, s.0.version) == s.0;
      } else if e :| (e in fdeps && e.1.feats == {} && ed == (e.0, Dep(e.1.name, e.1.versions))) {
      } else if e, f :| (e in fdeps && f in e.1.feats
           && ed == (e.0, Dep(FeatureName(e.1.name, f), e.1.versions))) {
        forall v | v in ed.1.versions
          ensures Package(ed.1.name, v) in repoF
        {
          assert (Package(e.1.name, v), f) in fsupp;
          assert Package(FeatureName(e.1.name, f), v) in FeatPkgs(fsupp);
        }
      } else if a :| (a in adeps && a.1.feats == {}
           && ed == (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version), Dep(a.1.name, a.1.versions))) {
        assert ed.0 in repoF by {
          AddSourceInRepo(repo, fsupp, adeps, a);
        }
      } else {
        var a, f :| a in adeps && f in a.1.feats
              && ed == (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                        Dep(FeatureName(a.1.name, f), a.1.versions));
        assert ed.0 in repoF by {
          AddSourceInRepo(repo, fsupp, adeps, a);
        }
        forall v | v in ed.1.versions
          ensures Package(ed.1.name, v) in repoF
        {
          assert (Package(a.1.name, v), f) in fsupp;
          assert Package(FeatureName(a.1.name, f), v) in FeatPkgs(fsupp);
        }
      }
    }
  }

  // The source of an additional-dependency edge exists in the reduced
  // repository whenever the owner supports the feature. We require that
  // explicitly as a well-formedness condition of A.
  predicate WfAddOwners(fsupp: SupportRel, adeps: AddDepRel) {
    forall a | a in adeps :: (a.0.0, a.0.1) in fsupp
  }

  lemma AddSourceInRepo(repo: set<Package>, fsupp: SupportRel, adeps: AddDepRel,
                        a: ((Package, Feature), FDep))
    requires WfAddOwners(fsupp, adeps)
    requires a in adeps
    ensures Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version) in FeatReduceRepo(repo, fsupp)
  {
    assert (a.0.0, a.0.1) in fsupp;
    assert Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version) in FeatPkgs(fsupp);
  }

  lemma FeatDepsNonempty(fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel)
    requires CFNonempty(fdeps, adeps)
    ensures NonemptyDeps(FeatReduceDeps(fsupp, fdeps, adeps))
  {
    forall ed | ed in FeatReduceDeps(fsupp, fdeps, adeps)
      ensures ed.1.versions != {}
    {
      FeatEdgeDecode(fsupp, fdeps, adeps, ed);
    }
  }

  @IsolateAssertions
  lemma FeatDepsUnique(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires WfSupp(repo, fsupp)
    requires CFUniqueDeps(fdeps) && CFUniqueAdds(adeps) && CFAddNotSelf(adeps)
    ensures UniqueDepPerName(FeatReduceDeps(fsupp, fdeps, adeps))
  {
    var depsF := FeatReduceDeps(fsupp, fdeps, adeps);
    forall ed1, ed2 | ed1 in depsF && ed2 in depsF
        && ed1.0 == ed2.0 && ed1.1.name == ed2.1.name
      ensures ed1.1 == ed2.1
    {
      FeatEdgeDecode(fsupp, fdeps, adeps, ed1);
      FeatEdgeDecode(fsupp, fdeps, adeps, ed2);
      EdgePairUnique(repo, fsupp, fdeps, adeps, ed1, ed2);
    }
  }

  @IsolateAssertions
  lemma EdgePairUnique(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                       ed1: (Package, Dep), ed2: (Package, Dep))
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires WfSupp(repo, fsupp)
    requires CFUniqueDeps(fdeps) && CFUniqueAdds(adeps) && CFAddNotSelf(adeps)
    requires ed1 in FeatReduceDeps(fsupp, fdeps, adeps)
    requires ed2 in FeatReduceDeps(fsupp, fdeps, adeps)
    requires ed1.0 == ed2.0 && ed1.1.name == ed2.1.name
    ensures ed1.1 == ed2.1
  {
    FeatEdgeDecode(fsupp, fdeps, adeps, ed1);
    FeatEdgeDecode(fsupp, fdeps, adeps, ed2);
    if !ed1.0.name.FeatureName? {
      // Plain sources: both edges are parameterised-dependency edges.
      if e1 :| (e1 in fdeps && e1.1.feats == {} && ed1 == (e1.0, Dep(e1.1.name, e1.1.versions))) {
        var e2 :| e2 in fdeps && e2.1.feats == {} && ed2 == (e2.0, Dep(e2.1.name, e2.1.versions));
        assert e1.1 == e2.1;  // CFUniqueDeps
      } else {
        var e1, f1 :| e1 in fdeps && f1 in e1.1.feats
              && ed1 == (e1.0, Dep(FeatureName(e1.1.name, f1), e1.1.versions));
        var e2, f2 :| e2 in fdeps && f2 in e2.1.feats
              && ed2 == (e2.0, Dep(FeatureName(e2.1.name, f2), e2.1.versions));
        assert e1.1.name == e2.1.name;
        assert e1.1 == e2.1;  // CFUniqueDeps
      }
    } else {
      // Feature-package sources: base or additional edges.
      if s1 :| (s1 in fsupp
           && ed1 == (Package(FeatureName(s1.0.name, s1.1), s1.0.version), Dep(s1.0.name, {s1.0.version}))) {
        // ed2 has the same plain target name, so it is also a base edge
        // (additional plain targets differ by CFAddNotSelf).
        if s2 :| (s2 in fsupp
             && ed2 == (Package(FeatureName(s2.0.name, s2.1), s2.0.version), Dep(s2.0.name, {s2.0.version}))) {
          assert s1.0.version == s2.0.version;
        } else if a2 :| (a2 in adeps && a2.1.feats == {}
             && ed2 == (Package(FeatureName(a2.0.0.name, a2.0.1), a2.0.0.version), Dep(a2.1.name, a2.1.versions))) {
          assert a2.0.0.name == s1.0.name && a2.1.name == s1.0.name;
          assert false;  // CFAddNotSelf
        } else {
          var a2, f2 :| a2 in adeps && f2 in a2.1.feats
                && ed2 == (Package(FeatureName(a2.0.0.name, a2.0.1), a2.0.0.version),
                           Dep(FeatureName(a2.1.name, f2), a2.1.versions));
          assert false;  // plain target vs FeatureName target
        }
      } else if a1 :| (a1 in adeps && a1.1.feats == {}
           && ed1 == (Package(FeatureName(a1.0.0.name, a1.0.1), a1.0.0.version), Dep(a1.1.name, a1.1.versions))) {
        if s2 :| (s2 in fsupp
             && ed2 == (Package(FeatureName(s2.0.name, s2.1), s2.0.version), Dep(s2.0.name, {s2.0.version}))) {
          assert a1.0.0.name == s2.0.name && a1.1.name == s2.0.name;
          assert false;  // CFAddNotSelf
        } else if a2 :| (a2 in adeps && a2.1.feats == {}
             && ed2 == (Package(FeatureName(a2.0.0.name, a2.0.1), a2.0.0.version), Dep(a2.1.name, a2.1.versions))) {
          assert a1.0.0 == Package(a1.0.0.name, a1.0.0.version);
          assert a2.0.0 == Package(a2.0.0.name, a2.0.0.version);
          assert a1.0 == a2.0;
          assert a1.1 == a2.1;  // CFUniqueAdds
        } else {
          var a2, f2 :| a2 in adeps && f2 in a2.1.feats
                && ed2 == (Package(FeatureName(a2.0.0.name, a2.0.1), a2.0.0.version),
                           Dep(FeatureName(a2.1.name, f2), a2.1.versions));
          assert false;  // plain target vs FeatureName target
        }
      } else {
        var a1, f1 :| a1 in adeps && f1 in a1.1.feats
              && ed1 == (Package(FeatureName(a1.0.0.name, a1.0.1), a1.0.0.version),
                         Dep(FeatureName(a1.1.name, f1), a1.1.versions));
        if s2 :| (s2 in fsupp
             && ed2 == (Package(FeatureName(s2.0.name, s2.1), s2.0.version), Dep(s2.0.name, {s2.0.version}))) {
          assert false;  // FeatureName target vs plain target
        } else if a2 :| (a2 in adeps && a2.1.feats == {}
             && ed2 == (Package(FeatureName(a2.0.0.name, a2.0.1), a2.0.0.version), Dep(a2.1.name, a2.1.versions))) {
          assert false;
        } else {
          var a2, f2 :| a2 in adeps && f2 in a2.1.feats
                && ed2 == (Package(FeatureName(a2.0.0.name, a2.0.1), a2.0.0.version),
                           Dep(FeatureName(a2.1.name, f2), a2.1.versions));
          assert a1.0.0 == Package(a1.0.0.name, a1.0.0.version);
          assert a2.0.0 == Package(a2.0.0.name, a2.0.0.version);
          assert a1.0 == a2.0;
          assert a1.1.name == a2.1.name;
          assert a1.1 == a2.1;  // CFUniqueAdds
        }
      }
    }
  }

  // ---------------------------------------------------------------------
  // The bridge: a Concurrent Feature resolution induces a concurrent
  // resolution of the feature-reduced instance.
  // ---------------------------------------------------------------------

  // ρ pairs with a plain parent and plain child name come from selP.
  lemma RhoPlainPlain(rf: FRes, selP: ParamSel, selA: AddSel,
                      fdeps: FDepRel, adeps: AddDepRel, repo: set<Package>,
                      fsupp: SupportRel,
                      child: Package, parent: Package)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires FResInRepo(repo, fsupp, rf)
    requires !parent.name.FeatureName? && !child.name.FeatureName?
    requires (child, parent) in ConcFeatRho(rf, selP, selA, fdeps, adeps)
    ensures exists e | e in fdeps ::
      e.0 == parent && e.1.name == child.name && e.1.feats == {}
      && ((e.0, e.1), child.version) in selP
  {
    if (child, parent) in CFRhoBase(rf) {
      var e, f :| e in rf && f in e.1
            && (child, parent) == (e.0, Package(FeatureName(e.0.name, f), e.0.version));
      assert false;
    } else if (child, parent) in CFRhoParamPlain(fdeps, selP) {
      var e, v :| e in fdeps && e.1.feats == {} && v in e.1.versions
            && ((e.0, e.1), v) in selP
            && (child, parent) == (Package(e.1.name, v), e.0);
    } else if (child, parent) in CFRhoParamFeat(fdeps, selP) {
      var e, f, v :| e in fdeps && f in e.1.feats && v in e.1.versions
            && ((e.0, e.1), v) in selP
            && (child, parent) == (Package(FeatureName(e.1.name, f), v), e.0);
      assert false;
    } else if (child, parent) in CFRhoAddPlain(adeps, selA) {
      var a, v :| a in adeps && a.1.feats == {} && v in a.1.versions
            && ((a.0, a.1), v) in selA
            && (child, parent) == (Package(a.1.name, v),
                                   Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version));
      assert false;
    } else {
      var a, f, v :| a in adeps && f in a.1.feats && v in a.1.versions
            && ((a.0, a.1), v) in selA
            && (child, parent) == (Package(FeatureName(a.1.name, f), v),
                                   Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version));
      assert false;
    }
  }

  // ρ pairs with a plain parent and feature-named child come from selP's
  // feature edges.
  lemma RhoPlainFeat(rf: FRes, selP: ParamSel, selA: AddSel,
                     fdeps: FDepRel, adeps: AddDepRel, repo: set<Package>,
                     fsupp: SupportRel,
                     child: Package, parent: Package)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires FResInRepo(repo, fsupp, rf)
    requires !parent.name.FeatureName? && child.name.FeatureName?
    requires (child, parent) in ConcFeatRho(rf, selP, selA, fdeps, adeps)
    ensures exists e, f | e in fdeps && f in e.1.feats ::
      e.0 == parent && FeatureName(e.1.name, f) == child.name
      && ((e.0, e.1), child.version) in selP
  {
    if (child, parent) in CFRhoBase(rf) {
      var e, f :| e in rf && f in e.1
            && (child, parent) == (e.0, Package(FeatureName(e.0.name, f), e.0.version));
      assert false;
    } else if (child, parent) in CFRhoParamPlain(fdeps, selP) {
      var e, v :| e in fdeps && e.1.feats == {} && v in e.1.versions
            && ((e.0, e.1), v) in selP
            && (child, parent) == (Package(e.1.name, v), e.0);
      assert false;
    } else if (child, parent) in CFRhoParamFeat(fdeps, selP) {
      var e, f, v :| e in fdeps && f in e.1.feats && v in e.1.versions
            && ((e.0, e.1), v) in selP
            && (child, parent) == (Package(FeatureName(e.1.name, f), v), e.0);
    } else if (child, parent) in CFRhoAddPlain(adeps, selA) {
      var a, v :| a in adeps && a.1.feats == {} && v in a.1.versions
            && ((a.0, a.1), v) in selA
            && (child, parent) == (Package(a.1.name, v),
                                   Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version));
      assert false;
    } else {
      var a, f, v :| a in adeps && f in a.1.feats && v in a.1.versions
            && ((a.0, a.1), v) in selA
            && (child, parent) == (Package(FeatureName(a.1.name, f), v),
                                   Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version));
      assert false;
    }
  }

  // ρ pairs with a feature-named parent and plain child distinct from the
  // owner's name come from selA's plain edges.
  lemma RhoFeatPlain(rf: FRes, selP: ParamSel, selA: AddSel,
                     fdeps: FDepRel, adeps: AddDepRel, repo: set<Package>,
                     fsupp: SupportRel,
                     child: Package, parent: Package)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires FResInRepo(repo, fsupp, rf)
    requires parent.name.FeatureName? && !child.name.FeatureName?
    requires child.name != parent.name.fbase
    requires (child, parent) in ConcFeatRho(rf, selP, selA, fdeps, adeps)
    ensures exists a | a in adeps ::
      Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version) == parent
      && a.1.name == child.name && a.1.feats == {}
      && ((a.0, a.1), child.version) in selA
  {
    if (child, parent) in CFRhoBase(rf) {
      var e, f :| e in rf && f in e.1
            && (child, parent) == (e.0, Package(FeatureName(e.0.name, f), e.0.version));
      assert parent.name.fbase == e.0.name && child.name == e.0.name;
      assert false;  // the base child carries the owner's name
    } else if (child, parent) in CFRhoParamPlain(fdeps, selP) {
      var e, v :| e in fdeps && e.1.feats == {} && v in e.1.versions
            && ((e.0, e.1), v) in selP
            && (child, parent) == (Package(e.1.name, v), e.0);
      assert e.0 in repo && !e.0.name.FeatureName?;
      assert false;
    } else if (child, parent) in CFRhoParamFeat(fdeps, selP) {
      var e, f, v :| e in fdeps && f in e.1.feats && v in e.1.versions
            && ((e.0, e.1), v) in selP
            && (child, parent) == (Package(FeatureName(e.1.name, f), v), e.0);
      assert e.0 in repo && !e.0.name.FeatureName?;
      assert false;
    } else if (child, parent) in CFRhoAddPlain(adeps, selA) {
      var a, v :| a in adeps && a.1.feats == {} && v in a.1.versions
            && ((a.0, a.1), v) in selA
            && (child, parent) == (Package(a.1.name, v),
                                   Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version));
    } else {
      var a, f, v :| a in adeps && f in a.1.feats && v in a.1.versions
            && ((a.0, a.1), v) in selA
            && (child, parent) == (Package(FeatureName(a.1.name, f), v),
                                   Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version));
      assert false;
    }
  }

  // ρ pairs with a feature-named parent and feature-named child come from
  // selA's feature edges.
  lemma RhoFeatFeat(rf: FRes, selP: ParamSel, selA: AddSel,
                    fdeps: FDepRel, adeps: AddDepRel, repo: set<Package>,
                    fsupp: SupportRel,
                    child: Package, parent: Package)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires FResInRepo(repo, fsupp, rf)
    requires parent.name.FeatureName? && child.name.FeatureName?
    requires (child, parent) in ConcFeatRho(rf, selP, selA, fdeps, adeps)
    ensures exists a, f | a in adeps && f in a.1.feats ::
      Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version) == parent
      && FeatureName(a.1.name, f) == child.name
      && ((a.0, a.1), child.version) in selA
  {
    if (child, parent) in CFRhoBase(rf) {
      var e, f :| e in rf && f in e.1
            && (child, parent) == (e.0, Package(FeatureName(e.0.name, f), e.0.version));
      assert e.0 in repo && !e.0.name.FeatureName?;
      assert false;  // base children are plain (FResInRepo + plain repo)
    } else if (child, parent) in CFRhoParamPlain(fdeps, selP) {
      var e, v :| e in fdeps && e.1.feats == {} && v in e.1.versions
            && ((e.0, e.1), v) in selP
            && (child, parent) == (Package(e.1.name, v), e.0);
      assert e.0 in repo && !e.0.name.FeatureName?;
      assert false;
    } else if (child, parent) in CFRhoParamFeat(fdeps, selP) {
      var e, f, v :| e in fdeps && f in e.1.feats && v in e.1.versions
            && ((e.0, e.1), v) in selP
            && (child, parent) == (Package(FeatureName(e.1.name, f), v), e.0);
      assert e.0 in repo && !e.0.name.FeatureName?;
      assert false;
    } else if (child, parent) in CFRhoAddPlain(adeps, selA) {
      var a, v :| a in adeps && a.1.feats == {} && v in a.1.versions
            && ((a.0, a.1), v) in selA
            && (child, parent) == (Package(a.1.name, v),
                                   Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version));
      assert false;
    } else {
      var a, f, v :| a in adeps && f in a.1.feats && v in a.1.versions
            && ((a.0, a.1), v) in selA
            && (child, parent) == (Package(FeatureName(a.1.name, f), v),
                                   Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version));
    }
  }

  // ---------------------------------------------------------------------
  // The bridge, edge kind by edge kind.
  // ---------------------------------------------------------------------

  // Base edges select exactly the accompanying base package.
  lemma BridgeBaseEdge(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                       rf: FRes, selP: ParamSel, selA: AddSel, s: (Package, Feature))
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires FResInRepo(repo, fsupp, rf)
    requires s in fsupp
    requires Package(FeatureName(s.0.name, s.1), s.0.version) in FeatBuildCore(rf)
    ensures var ed := (Package(FeatureName(s.0.name, s.1), s.0.version), Dep(s.0.name, {s.0.version}));
      (exists v | v in ed.1.versions ::
         Selected(ed, v, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps)))
      && (forall v1, v2 | v1 in ed.1.versions && v2 in ed.1.versions :: v1 == v2)
  {
    var rFeat := FeatBuildCore(rf);
    var rho := ConcFeatRho(rf, selP, selA, fdeps, adeps);
    var ed := (Package(FeatureName(s.0.name, s.1), s.0.version), Dep(s.0.name, {s.0.version}));
    assert forall e | e in rf :: e.0 in repo;
    FeaturesLemmas.BuildFeatDecode(repo, rf, ed.0);
    var e :| e in rf && e.0 == Package(ed.0.name.fbase, ed.0.version) && ed.0.name.feat in e.1;
    assert e.0 == Package(s.0.name, s.0.version);
    assert e.0 in rFeat;
    assert (e.0, Package(FeatureName(e.0.name, s.1), e.0.version)) in CFRhoBase(rf);
    assert Package(FeatureName(e.0.name, s.1), e.0.version) == ed.0;
    assert Selected(ed, s.0.version, rFeat, rho);
  }

  // Parameterised dependencies without features select via selP.
  lemma BridgeParamPlainEdge(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                             rf: FRes, selP: ParamSel, selA: AddSel, e: (Package, FDep))
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires FResInRepo(repo, fsupp, rf)
    requires CFUniqueDeps(fdeps) && FunctionalP(selP)
    requires CFParamClosure(fdeps, rf, selP)
    requires e in fdeps && e.1.feats == {}
    requires e.0 in FeatBuildCore(rf)
    ensures var ed := (e.0, Dep(e.1.name, e.1.versions));
      (exists v | v in ed.1.versions ::
         Selected(ed, v, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps)))
      && (forall v1, v2 | v1 in ed.1.versions && v2 in ed.1.versions
            && Selected(ed, v1, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps))
            && Selected(ed, v2, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps))
            :: v1 == v2)
  {
    var rFeat := FeatBuildCore(rf);
    var rho := ConcFeatRho(rf, selP, selA, fdeps, adeps);
    var ed := (e.0, Dep(e.1.name, e.1.versions));
    assert forall q | q in rf :: q.0 in repo;
    FeaturesLemmas.SourceEntry(repo, fsupp, rf, e.0);
    var pe :| pe in rf && pe.0 == e.0;
    var v :| v in e.1.versions && ((e.0, e.1), v) in selP && CFSelected(rf, e.1, v);
    var q :| q in rf && q.0 == Package(e.1.name, v) && e.1.feats <= q.1;
    assert q.0 in rFeat;
    assert (Package(e.1.name, v), e.0) in CFRhoParamPlain(fdeps, selP);
    assert Selected(ed, v, rFeat, rho);

    forall v1, v2 | v1 in ed.1.versions && v2 in ed.1.versions
          && Selected(ed, v1, rFeat, rho) && Selected(ed, v2, rFeat, rho)
      ensures v1 == v2
    {
      ParamPlainSelUnique(repo, fsupp, fdeps, adeps, rf, selP, selA, e, v1);
      ParamPlainSelUnique(repo, fsupp, fdeps, adeps, rf, selP, selA, e, v2);
    }
  }

  lemma ParamPlainSelUnique(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                            rf: FRes, selP: ParamSel, selA: AddSel,
                            e: (Package, FDep), v: Version)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires FResInRepo(repo, fsupp, rf)
    requires CFUniqueDeps(fdeps)
    requires e in fdeps
    requires (Package(e.1.name, v), e.0) in ConcFeatRho(rf, selP, selA, fdeps, adeps)
    ensures ((e.0, e.1), v) in selP
  {
    assert !e.0.name.FeatureName? && !e.1.name.FeatureName?;
    RhoPlainPlain(rf, selP, selA, fdeps, adeps, repo, fsupp, Package(e.1.name, v), e.0);
    var e' :| e' in fdeps && e'.0 == e.0 && e'.1.name == e.1.name && e'.1.feats == {}
          && ((e'.0, e'.1), v) in selP;
    assert e'.1 == e.1;  // CFUniqueDeps
  }

  // Parameterised dependencies with a required feature select the feature
  // package at the selP version.
  lemma BridgeParamFeatEdge(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                            rf: FRes, selP: ParamSel, selA: AddSel,
                            e: (Package, FDep), f: Feature)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires FResInRepo(repo, fsupp, rf)
    requires CFUniqueDeps(fdeps) && FunctionalP(selP)
    requires CFParamClosure(fdeps, rf, selP)
    requires e in fdeps && f in e.1.feats
    requires e.0 in FeatBuildCore(rf)
    ensures var ed := (e.0, Dep(FeatureName(e.1.name, f), e.1.versions));
      (exists v | v in ed.1.versions ::
         Selected(ed, v, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps)))
      && (forall v1, v2 | v1 in ed.1.versions && v2 in ed.1.versions
            && Selected(ed, v1, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps))
            && Selected(ed, v2, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps))
            :: v1 == v2)
  {
    var rFeat := FeatBuildCore(rf);
    var rho := ConcFeatRho(rf, selP, selA, fdeps, adeps);
    var ed := (e.0, Dep(FeatureName(e.1.name, f), e.1.versions));
    assert forall q | q in rf :: q.0 in repo;
    FeaturesLemmas.SourceEntry(repo, fsupp, rf, e.0);
    var pe :| pe in rf && pe.0 == e.0;
    var v :| v in e.1.versions && ((e.0, e.1), v) in selP && CFSelected(rf, e.1, v);
    var q :| q in rf && q.0 == Package(e.1.name, v) && e.1.feats <= q.1;
    assert Package(FeatureName(q.0.name, f), q.0.version) in FeatBuildCore(rf);
    assert Package(FeatureName(q.0.name, f), q.0.version) == Package(FeatureName(e.1.name, f), v);
    assert (Package(FeatureName(e.1.name, f), v), e.0) in CFRhoParamFeat(fdeps, selP);
    assert Selected(ed, v, rFeat, rho);

    forall v1, v2 | v1 in ed.1.versions && v2 in ed.1.versions
          && Selected(ed, v1, rFeat, rho) && Selected(ed, v2, rFeat, rho)
      ensures v1 == v2
    {
      ParamFeatSelUnique(repo, fsupp, fdeps, adeps, rf, selP, selA, e, f, v1);
      ParamFeatSelUnique(repo, fsupp, fdeps, adeps, rf, selP, selA, e, f, v2);
    }
  }

  lemma ParamFeatSelUnique(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                           rf: FRes, selP: ParamSel, selA: AddSel,
                           e: (Package, FDep), f: Feature, v: Version)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires FResInRepo(repo, fsupp, rf)
    requires CFUniqueDeps(fdeps)
    requires e in fdeps
    requires (Package(FeatureName(e.1.name, f), v), e.0) in ConcFeatRho(rf, selP, selA, fdeps, adeps)
    ensures ((e.0, e.1), v) in selP
  {
    assert !e.0.name.FeatureName?;
    RhoPlainFeat(rf, selP, selA, fdeps, adeps, repo, fsupp, Package(FeatureName(e.1.name, f), v), e.0);
    var e', f' :| e' in fdeps && f' in e'.1.feats && e'.0 == e.0
          && FeatureName(e'.1.name, f') == FeatureName(e.1.name, f)
          && ((e'.0, e'.1), v) in selP;
    assert e'.1 == e.1;  // CFUniqueDeps
  }

  // Additional dependencies without features.
  lemma BridgeAddPlainEdge(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                           rf: FRes, selP: ParamSel, selA: AddSel, a: ((Package, Feature), FDep))
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires FResInRepo(repo, fsupp, rf)
    requires CFUniqueAdds(adeps) && CFAddNotSelf(adeps) && FunctionalA(selA)
    requires CFAddClosure(adeps, rf, selA)
    requires a in adeps && a.1.feats == {}
    requires Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version) in FeatBuildCore(rf)
    ensures var ed := (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version), Dep(a.1.name, a.1.versions));
      (exists v | v in ed.1.versions ::
         Selected(ed, v, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps)))
      && (forall v1, v2 | v1 in ed.1.versions && v2 in ed.1.versions
            && Selected(ed, v1, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps))
            && Selected(ed, v2, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps))
            :: v1 == v2)
  {
    var rFeat := FeatBuildCore(rf);
    var rho := ConcFeatRho(rf, selP, selA, fdeps, adeps);
    var ed := (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version), Dep(a.1.name, a.1.versions));
    assert forall q | q in rf :: q.0 in repo;
    FeaturesLemmas.BuildFeatDecode(repo, rf, ed.0);
    var pe :| pe in rf && pe.0 == Package(ed.0.name.fbase, ed.0.version) && ed.0.name.feat in pe.1;
    assert pe.0 == a.0.0 && a.0.1 in pe.1;
    var v :| v in a.1.versions && ((a.0, a.1), v) in selA && CFSelected(rf, a.1, v);
    var q :| q in rf && q.0 == Package(a.1.name, v) && a.1.feats <= q.1;
    assert q.0 in rFeat;
    assert (Package(a.1.name, v), ed.0) in CFRhoAddPlain(adeps, selA);
    assert Selected(ed, v, rFeat, rho);

    forall v1, v2 | v1 in ed.1.versions && v2 in ed.1.versions
          && Selected(ed, v1, rFeat, rho) && Selected(ed, v2, rFeat, rho)
      ensures v1 == v2
    {
      AddPlainSelUnique(repo, fsupp, fdeps, adeps, rf, selP, selA, a, v1);
      AddPlainSelUnique(repo, fsupp, fdeps, adeps, rf, selP, selA, a, v2);
    }
  }

  lemma AddPlainSelUnique(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                          rf: FRes, selP: ParamSel, selA: AddSel,
                          a: ((Package, Feature), FDep), v: Version)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires FResInRepo(repo, fsupp, rf)
    requires CFUniqueAdds(adeps) && CFAddNotSelf(adeps)
    requires a in adeps
    requires (Package(a.1.name, v), Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version))
             in ConcFeatRho(rf, selP, selA, fdeps, adeps)
    ensures ((a.0, a.1), v) in selA
  {
    var parent := Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version);
    assert !a.1.name.FeatureName?;
    assert a.1.name != parent.name.fbase;  // CFAddNotSelf
    RhoFeatPlain(rf, selP, selA, fdeps, adeps, repo, fsupp, Package(a.1.name, v), parent);
    var a' :| a' in adeps
          && Package(FeatureName(a'.0.0.name, a'.0.1), a'.0.0.version) == parent
          && a'.1.name == a.1.name && a'.1.feats == {}
          && ((a'.0, a'.1), v) in selA;
    assert a'.0.0 == Package(a'.0.0.name, a'.0.0.version);
    assert a.0.0 == Package(a.0.0.name, a.0.0.version);
    assert a'.0 == a.0;
    assert a'.1 == a.1;  // CFUniqueAdds
  }

  // Additional dependencies with a required feature.
  lemma BridgeAddFeatEdge(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                          rf: FRes, selP: ParamSel, selA: AddSel,
                          a: ((Package, Feature), FDep), f: Feature)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires FResInRepo(repo, fsupp, rf)
    requires CFUniqueAdds(adeps) && CFAddNotSelf(adeps) && FunctionalA(selA)
    requires CFAddClosure(adeps, rf, selA)
    requires a in adeps && f in a.1.feats
    requires Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version) in FeatBuildCore(rf)
    ensures var ed := (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                       Dep(FeatureName(a.1.name, f), a.1.versions));
      (exists v | v in ed.1.versions ::
         Selected(ed, v, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps)))
      && (forall v1, v2 | v1 in ed.1.versions && v2 in ed.1.versions
            && Selected(ed, v1, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps))
            && Selected(ed, v2, FeatBuildCore(rf), ConcFeatRho(rf, selP, selA, fdeps, adeps))
            :: v1 == v2)
  {
    var rFeat := FeatBuildCore(rf);
    var rho := ConcFeatRho(rf, selP, selA, fdeps, adeps);
    var ed := (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
               Dep(FeatureName(a.1.name, f), a.1.versions));
    assert forall q | q in rf :: q.0 in repo;
    FeaturesLemmas.BuildFeatDecode(repo, rf, ed.0);
    var pe :| pe in rf && pe.0 == Package(ed.0.name.fbase, ed.0.version) && ed.0.name.feat in pe.1;
    assert pe.0 == a.0.0 && a.0.1 in pe.1;
    var v :| v in a.1.versions && ((a.0, a.1), v) in selA && CFSelected(rf, a.1, v);
    var q :| q in rf && q.0 == Package(a.1.name, v) && a.1.feats <= q.1;
    assert Package(FeatureName(q.0.name, f), q.0.version) in FeatBuildCore(rf);
    assert Package(FeatureName(q.0.name, f), q.0.version) == Package(FeatureName(a.1.name, f), v);
    assert (Package(FeatureName(a.1.name, f), v), ed.0) in CFRhoAddFeat(adeps, selA);
    assert Selected(ed, v, rFeat, rho);

    forall v1, v2 | v1 in ed.1.versions && v2 in ed.1.versions
          && Selected(ed, v1, rFeat, rho) && Selected(ed, v2, rFeat, rho)
      ensures v1 == v2
    {
      AddFeatSelUnique(repo, fsupp, fdeps, adeps, rf, selP, selA, a, f, v1);
      AddFeatSelUnique(repo, fsupp, fdeps, adeps, rf, selP, selA, a, f, v2);
    }
  }

  lemma AddFeatSelUnique(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                         rf: FRes, selP: ParamSel, selA: AddSel,
                         a: ((Package, Feature), FDep), f: Feature, v: Version)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires FResInRepo(repo, fsupp, rf)
    requires CFUniqueAdds(adeps)
    requires a in adeps
    requires (Package(FeatureName(a.1.name, f), v), Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version))
             in ConcFeatRho(rf, selP, selA, fdeps, adeps)
    ensures ((a.0, a.1), v) in selA
  {
    var parent := Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version);
    RhoFeatFeat(rf, selP, selA, fdeps, adeps, repo, fsupp, Package(FeatureName(a.1.name, f), v), parent);
    var a', f' :| a' in adeps && f' in a'.1.feats
          && Package(FeatureName(a'.0.0.name, a'.0.1), a'.0.0.version) == parent
          && FeatureName(a'.1.name, f') == FeatureName(a.1.name, f)
          && ((a'.0, a'.1), v) in selA;
    assert a'.0.0 == Package(a'.0.0.name, a'.0.0.version);
    assert a.0.0 == Package(a.0.0.name, a.0.0.version);
    assert a'.0 == a.0;
    assert a'.1 == a.1;  // CFUniqueAdds
  }

  // ---------------------------------------------------------------------
  // The bridge and Theorem 5.2.3.
  // ---------------------------------------------------------------------

  lemma BridgeGranularity(repo: set<Package>, fsupp: SupportRel, g: GranFn, rf: FRes)
    requires forall p | p in repo :: !p.name.FeatureName?
    requires FResInRepo(repo, fsupp, rf)
    requires CFGranularity(g, rf)
    ensures VersionGranularity(g, FeatBuildCore(rf))
  {
    var rFeat := FeatBuildCore(rf);
    forall p, q | p in rFeat && q in rFeat && p.name == q.name && p.version != q.version
      ensures g(p.version) != g(q.version)
    {
      if p in (set e | e in rf :: e.0) && q in (set e | e in rf :: e.0) {
        var e1 :| e1 in rf && p == e1.0;
        var e2 :| e2 in rf && q == e2.0;
      } else if p !in (set e | e in rf :: e.0) && q !in (set e | e in rf :: e.0) {
        var e1, f1 :| e1 in rf && f1 in e1.1 && p == Package(FeatureName(e1.0.name, f1), e1.0.version);
        var e2, f2 :| e2 in rf && f2 in e2.1 && q == Package(FeatureName(e2.0.name, f2), e2.0.version);
        assert e1.0.name == e2.0.name;
        assert e1.0.version == p.version && e2.0.version == q.version;
      } else if p in (set e | e in rf :: e.0) {
        var e1 :| e1 in rf && p == e1.0;
        var e2, f2 :| e2 in rf && f2 in e2.1 && q == Package(FeatureName(e2.0.name, f2), e2.0.version);
        assert e1.0 in repo;
        assert false;  // plain vs FeatureName
      } else {
        var e1, f1 :| e1 in rf && f1 in e1.1 && p == Package(FeatureName(e1.0.name, f1), e1.0.version);
        var e2 :| e2 in rf && q == e2.0;
        assert e2.0 in repo;
        assert false;
      }
    }
  }

  @IsolateAssertions
  lemma Bridge(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
               g: GranFn, root: Package, rf: FRes, selP: ParamSel, selA: AddSel)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires WfAddDeps(repo, fsupp, adeps)
    requires WfSupp(repo, fsupp)
    requires CFUniqueDeps(fdeps) && CFUniqueAdds(adeps) && CFAddNotSelf(adeps)
    requires root in repo
    requires ValidConcFeatResolution(repo, fsupp, fdeps, adeps, g, root, rf, selP, selA)
    ensures ValidConcurrentResolution(FeatReduceRepo(repo, fsupp),
                                      FeatReduceDeps(fsupp, fdeps, adeps), g, root,
                                      FeatBuildCore(rf),
                                      ConcFeatRho(rf, selP, selA, fdeps, adeps))
  {
    var rFeat := FeatBuildCore(rf);
    var rho := ConcFeatRho(rf, selP, selA, fdeps, adeps);
    var depsF := FeatReduceDeps(fsupp, fdeps, adeps);

    // rFeat ⊆ reduced repository.
    forall p | p in rFeat
      ensures p in FeatReduceRepo(repo, fsupp)
    {
      if p in (set e | e in rf :: e.0) {
        var e :| e in rf && p == e.0;
        assert p in repo;
      } else {
        var e, f :| e in rf && f in e.1 && p == Package(FeatureName(e.0.name, f), e.0.version);
        assert (e.0, f) in fsupp;
        assert p in FeatPkgs(fsupp);
      }
    }

    // Root inclusion.
    var re :| re in rf && re.0 == root;
    assert root in rFeat;

    // Version granularity.
    BridgeGranularity(repo, fsupp, g, rf);

    // Parent closure, edge kind by edge kind.
    forall ed | ed in depsF && ed.0 in rFeat
      ensures (exists v | v in ed.1.versions :: Selected(ed, v, rFeat, rho))
           && (forall v1, v2 | v1 in ed.1.versions && v2 in ed.1.versions
                 && Selected(ed, v1, rFeat, rho) && Selected(ed, v2, rFeat, rho) :: v1 == v2)
    {
      FeatEdgeDecode(fsupp, fdeps, adeps, ed);
      if s :| (s in fsupp
           && ed == (Package(FeatureName(s.0.name, s.1), s.0.version), Dep(s.0.name, {s.0.version}))) {
        BridgeBaseEdge(repo, fsupp, fdeps, adeps, rf, selP, selA, s);
      } else if e :| (e in fdeps && e.1.feats == {} && ed == (e.0, Dep(e.1.name, e.1.versions))) {
        BridgeParamPlainEdge(repo, fsupp, fdeps, adeps, rf, selP, selA, e);
      } else if e, f :| (e in fdeps && f in e.1.feats
           && ed == (e.0, Dep(FeatureName(e.1.name, f), e.1.versions))) {
        BridgeParamFeatEdge(repo, fsupp, fdeps, adeps, rf, selP, selA, e, f);
      } else if a :| (a in adeps && a.1.feats == {}
           && ed == (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version), Dep(a.1.name, a.1.versions))) {
        BridgeAddPlainEdge(repo, fsupp, fdeps, adeps, rf, selP, selA, a);
      } else {
        var a, f :| a in adeps && f in a.1.feats
              && ed == (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                        Dep(FeatureName(a.1.name, f), a.1.versions));
        BridgeAddFeatEdge(repo, fsupp, fdeps, adeps, rf, selP, selA, a, f);
      }
    }
  }

  // ---------------------------------------------------------------------
  // The repaired Theorem 5.2.2: soundness under feature coherence.
  // ---------------------------------------------------------------------

  // Parents recorded by the concurrent extraction are themselves selected.
  lemma ParentInRg(r: set<Package>, deps: DepRel, g: GranFn, pr: (Package, Package))
    requires pr in ConcExtractRho(r, deps, g)
    ensures pr.1 in ConcExtractRes(r, g)
  {
    if pr in ConcRhoSplit(r, deps, g) {
      var e, gam, u :| e in deps && IsSplit(e, g)
            && gam in Grans(e.1.versions, g) && u in e.1.versions
            && GPkg(e.0, g) in r
            && Package(IName(e), gam) in r
            && Package(GranularName(e.1.name, gam), u) in r
            && pr == (Package(e.1.name, u), e.0);
      assert e.0 == Package(GPkg(e.0, g).name.gbase, GPkg(e.0, g).version);
    } else {
      var e, u :| e in deps && !IsSplit(e, g)
            && u in e.1.versions
            && GPkg(e.0, g) in r
            && Package(GranularName(e.1.name, g(u)), u) in r
            && pr == (Package(e.1.name, u), e.0);
      assert e.0 == Package(GPkg(e.0, g).name.gbase, GPkg(e.0, g).version);
    }
  }

  // The extracted parameterised selection is functional: within one
  // feature it is the parent closure's unique child; across features it
  // is feature coherence.
  lemma SelPFunctional(fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                       rg: set<Package>, rho: ParentRel)
    requires ParentClosure(FeatReduceDeps(fsupp, fdeps, adeps), rg, rho)
    requires forall pr | pr in rho :: pr.1 in rg
    requires FeatureCoherent(fdeps, adeps, rg, rho)
    ensures FunctionalP(CFExtractSelP(fdeps, rg, rho))
  {
    var selP := CFExtractSelP(fdeps, rg, rho);
    forall s1, s2 | s1 in selP && s2 in selP && s1.0 == s2.0
      ensures s1.1 == s2.1
    {
      SelPEntryUnique(fsupp, fdeps, adeps, rg, rho, s1, s2);
    }
  }

  lemma SelPEntryUnique(fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                        rg: set<Package>, rho: ParentRel,
                        s1: ((Package, FDep), Version), s2: ((Package, FDep), Version))
    requires ParentClosure(FeatReduceDeps(fsupp, fdeps, adeps), rg, rho)
    requires forall pr | pr in rho :: pr.1 in rg
    requires FeatureCoherent(fdeps, adeps, rg, rho)
    requires s1 in CFExtractSelP(fdeps, rg, rho)
    requires s2 in CFExtractSelP(fdeps, rg, rho)
    requires s1.0 == s2.0
    ensures s1.1 == s2.1
  {
    var plainPart := set e, v | e in fdeps && e.1.feats == {} && v in e.1.versions
       && Selected((e.0, Dep(e.1.name, e.1.versions)), v, rg, rho)
       :: ((e.0, e.1), v);
    if s1 in plainPart && s2 in plainPart {
      var e1, v1 :| e1 in fdeps && e1.1.feats == {} && v1 in e1.1.versions
            && Selected((e1.0, Dep(e1.1.name, e1.1.versions)), v1, rg, rho)
            && s1 == ((e1.0, e1.1), v1);
      var e2, v2 :| e2 in fdeps && e2.1.feats == {} && v2 in e2.1.versions
            && Selected((e2.0, Dep(e2.1.name, e2.1.versions)), v2, rg, rho)
            && s2 == ((e2.0, e2.1), v2);
      assert e1 == e2;
      var ed := (e1.0, Dep(e1.1.name, e1.1.versions));
      assert ed in FeatReduceDeps(fsupp, fdeps, adeps);
      assert ed.0 in rg;  // its ρ pair's parent is selected
      assert v1 == v2;    // parent closure uniqueness
    } else if s1 !in plainPart && s2 !in plainPart {
      var e1, f1, v1 :| e1 in fdeps && f1 in e1.1.feats && v1 in e1.1.versions
            && Selected((e1.0, Dep(FeatureName(e1.1.name, f1), e1.1.versions)), v1, rg, rho)
            && s1 == ((e1.0, e1.1), v1);
      var e2, f2, v2 :| e2 in fdeps && f2 in e2.1.feats && v2 in e2.1.versions
            && Selected((e2.0, Dep(FeatureName(e2.1.name, f2), e2.1.versions)), v2, rg, rho)
            && s2 == ((e2.0, e2.1), v2);
      assert e1 == e2;
      assert v1 == v2;  // feature coherence
    } else if s1 in plainPart {
      var e1, v1 :| e1 in fdeps && e1.1.feats == {} && v1 in e1.1.versions
            && Selected((e1.0, Dep(e1.1.name, e1.1.versions)), v1, rg, rho)
            && s1 == ((e1.0, e1.1), v1);
      var e2, f2, v2 :| e2 in fdeps && f2 in e2.1.feats && v2 in e2.1.versions
            && Selected((e2.0, Dep(FeatureName(e2.1.name, f2), e2.1.versions)), v2, rg, rho)
            && s2 == ((e2.0, e2.1), v2);
      assert e1.1 == e2.1 && e1.1.feats == {} && f2 in e2.1.feats;
      assert false;
    } else {
      var e1, f1, v1 :| e1 in fdeps && f1 in e1.1.feats && v1 in e1.1.versions
            && Selected((e1.0, Dep(FeatureName(e1.1.name, f1), e1.1.versions)), v1, rg, rho)
            && s1 == ((e1.0, e1.1), v1);
      var e2, v2 :| e2 in fdeps && e2.1.feats == {} && v2 in e2.1.versions
            && Selected((e2.0, Dep(e2.1.name, e2.1.versions)), v2, rg, rho)
            && s2 == ((e2.0, e2.1), v2);
      assert e1.1 == e2.1 && e2.1.feats == {} && f1 in e1.1.feats;
      assert false;
    }
  }

  // Likewise for the additional selection.
  lemma SelAFunctional(fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                       rg: set<Package>, rho: ParentRel)
    requires ParentClosure(FeatReduceDeps(fsupp, fdeps, adeps), rg, rho)
    requires forall pr | pr in rho :: pr.1 in rg
    requires FeatureCoherent(fdeps, adeps, rg, rho)
    ensures FunctionalA(CFExtractSelA(adeps, rg, rho))
  {
    var selA := CFExtractSelA(adeps, rg, rho);
    forall s1, s2 | s1 in selA && s2 in selA && s1.0 == s2.0
      ensures s1.1 == s2.1
    {
      SelAEntryUnique(fsupp, fdeps, adeps, rg, rho, s1, s2);
    }
  }

  lemma SelAEntryUnique(fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                        rg: set<Package>, rho: ParentRel,
                        s1: (((Package, Feature), FDep), Version), s2: (((Package, Feature), FDep), Version))
    requires ParentClosure(FeatReduceDeps(fsupp, fdeps, adeps), rg, rho)
    requires forall pr | pr in rho :: pr.1 in rg
    requires FeatureCoherent(fdeps, adeps, rg, rho)
    requires s1 in CFExtractSelA(adeps, rg, rho)
    requires s2 in CFExtractSelA(adeps, rg, rho)
    requires s1.0 == s2.0
    ensures s1.1 == s2.1
  {
    var plainPart := set a, v | a in adeps && a.1.feats == {} && v in a.1.versions
       && Selected((Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                    Dep(a.1.name, a.1.versions)), v, rg, rho)
       :: ((a.0, a.1), v);
    if s1 in plainPart && s2 in plainPart {
      var a1, v1 :| a1 in adeps && a1.1.feats == {} && v1 in a1.1.versions
            && Selected((Package(FeatureName(a1.0.0.name, a1.0.1), a1.0.0.version),
                         Dep(a1.1.name, a1.1.versions)), v1, rg, rho)
            && s1 == ((a1.0, a1.1), v1);
      var a2, v2 :| a2 in adeps && a2.1.feats == {} && v2 in a2.1.versions
            && Selected((Package(FeatureName(a2.0.0.name, a2.0.1), a2.0.0.version),
                         Dep(a2.1.name, a2.1.versions)), v2, rg, rho)
            && s2 == ((a2.0, a2.1), v2);
      assert a1 == a2;
      var ed := (Package(FeatureName(a1.0.0.name, a1.0.1), a1.0.0.version),
                 Dep(a1.1.name, a1.1.versions));
      assert ed in FeatReduceDeps(fsupp, fdeps, adeps);
      assert ed.0 in rg;
      assert v1 == v2;
    } else if s1 !in plainPart && s2 !in plainPart {
      var a1, f1, v1 :| a1 in adeps && f1 in a1.1.feats && v1 in a1.1.versions
            && Selected((Package(FeatureName(a1.0.0.name, a1.0.1), a1.0.0.version),
                         Dep(FeatureName(a1.1.name, f1), a1.1.versions)), v1, rg, rho)
            && s1 == ((a1.0, a1.1), v1);
      var a2, f2, v2 :| a2 in adeps && f2 in a2.1.feats && v2 in a2.1.versions
            && Selected((Package(FeatureName(a2.0.0.name, a2.0.1), a2.0.0.version),
                         Dep(FeatureName(a2.1.name, f2), a2.1.versions)), v2, rg, rho)
            && s2 == ((a2.0, a2.1), v2);
      assert a1 == a2;
      assert v1 == v2;  // feature coherence
    } else if s1 in plainPart {
      var a1, v1 :| a1 in adeps && a1.1.feats == {} && v1 in a1.1.versions
            && Selected((Package(FeatureName(a1.0.0.name, a1.0.1), a1.0.0.version),
                         Dep(a1.1.name, a1.1.versions)), v1, rg, rho)
            && s1 == ((a1.0, a1.1), v1);
      var a2, f2, v2 :| a2 in adeps && f2 in a2.1.feats && v2 in a2.1.versions
            && Selected((Package(FeatureName(a2.0.0.name, a2.0.1), a2.0.0.version),
                         Dep(FeatureName(a2.1.name, f2), a2.1.versions)), v2, rg, rho)
            && s2 == ((a2.0, a2.1), v2);
      assert a1.1 == a2.1;
      assert false;
    } else {
      var a1, f1, v1 :| a1 in adeps && f1 in a1.1.feats && v1 in a1.1.versions
            && Selected((Package(FeatureName(a1.0.0.name, a1.0.1), a1.0.0.version),
                         Dep(FeatureName(a1.1.name, f1), a1.1.versions)), v1, rg, rho)
            && s1 == ((a1.0, a1.1), v1);
      var a2, v2 :| a2 in adeps && a2.1.feats == {} && v2 in a2.1.versions
            && Selected((Package(FeatureName(a2.0.0.name, a2.0.1), a2.0.0.version),
                         Dep(a2.1.name, a2.1.versions)), v2, rg, rho)
            && s2 == ((a2.0, a2.1), v2);
      assert a1.1 == a2.1;
      assert false;
    }
  }

  // A satisfied dependency occurrence: the coherent selection pins one
  // version whose entry carries all required features.
  lemma DepOccurrenceSatisfied(repo: set<Package>, fsupp: SupportRel,
                               fdeps: FDepRel, adeps: AddDepRel,
                               rg: set<Package>, rho: ParentRel,
                               src: Package, d: FDep)
    requires forall p | p in repo :: !p.name.FeatureName?
    requires rg <= FeatReduceRepo(repo, fsupp)
    requires ParentClosure(FeatReduceDeps(fsupp, fdeps, adeps), rg, rho)
    requires src in rg
    requires d.feats == {} ==>
      (src, Dep(d.name, d.versions)) in FeatReduceDeps(fsupp, fdeps, adeps)
    requires forall f | f in d.feats ::
      (src, Dep(FeatureName(d.name, f), d.versions)) in FeatReduceDeps(fsupp, fdeps, adeps)
    requires forall f1, f2, v1, v2 |
      f1 in d.feats && f2 in d.feats && v1 in d.versions && v2 in d.versions
      && Selected((src, Dep(FeatureName(d.name, f1), d.versions)), v1, rg, rho)
      && Selected((src, Dep(FeatureName(d.name, f2), d.versions)), v2, rg, rho)
      :: v1 == v2
    requires !d.name.FeatureName?
    ensures exists v | v in d.versions ::
      CFSelected(FeatExtract(rg), d, v)
      && (d.feats == {} ==> Selected((src, Dep(d.name, d.versions)), v, rg, rho))
      && (forall f | f in d.feats ::
            Selected((src, Dep(FeatureName(d.name, f), d.versions)), v, rg, rho))
  {
    var rf := FeatExtract(rg);
    if d.feats == {} {
      var ed := (src, Dep(d.name, d.versions));
      var v :| v in ed.1.versions && Selected(ed, v, rg, rho);
      var child := Package(d.name, v);
      assert (child, FeatSelOf(rg, child)) in rf;
      assert CFSelected(rf, d, v);
    } else {
      var f0 :| f0 in d.feats;
      var ed0 := (src, Dep(FeatureName(d.name, f0), d.versions));
      var v :| v in ed0.1.versions && Selected(ed0, v, rg, rho);
      var fp0 := Package(FeatureName(d.name, f0), v);
      assert fp0 in rg;

      // The base edge of fp0 places the base package in rg.
      FeaturesLemmas.FeatPkgDecode(repo, fsupp, fp0);
      var s := (Package(d.name, v), f0);
      var bEdge := (fp0, Dep(d.name, {v}));
      assert bEdge == (Package(FeatureName(s.0.name, s.1), s.0.version), Dep(s.0.name, {s.0.version}));
      assert bEdge in FeatBaseEdges(fsupp);
      var w :| w in bEdge.1.versions && Selected(bEdge, w, rg, rho);
      assert w == v;
      var base := Package(d.name, v);
      assert base in rg;

      // Every required feature's package sits at the same version v.
      var q := (base, FeatSelOf(rg, base));
      assert q in rf;
      forall f | f in d.feats
        ensures f in q.1 && Selected((src, Dep(FeatureName(d.name, f), d.versions)), v, rg, rho)
      {
        var edf := (src, Dep(FeatureName(d.name, f), d.versions));
        var vf :| vf in edf.1.versions && Selected(edf, vf, rg, rho);
        assert vf == v;  // coherence hypothesis
        assert Package(FeatureName(d.name, f), v) in rg;
      }
      assert CFSelected(rf, d, v);
    }
  }

  // The repaired Theorem 5.2.2, from the concurrent level: a concurrent
  // resolution of the feature-reduced instance that is feature-coherent
  // extracts to a valid Concurrent Feature resolution.
  @IsolateAssertions
  lemma ConcFeatExtractSound(repo: set<Package>, fsupp: SupportRel,
                             fdeps: FDepRel, adeps: AddDepRel, g: GranFn,
                             root: Package, rg: set<Package>, rho: ParentRel)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires root in repo
    requires forall pr | pr in rho :: pr.1 in rg
    requires ValidConcurrentResolution(FeatReduceRepo(repo, fsupp),
                                       FeatReduceDeps(fsupp, fdeps, adeps), g, root, rg, rho)
    requires FeatureCoherent(fdeps, adeps, rg, rho)
    ensures ValidConcFeatResolution(repo, fsupp, fdeps, adeps, g, root,
                                    FeatExtract(rg),
                                    CFExtractSelP(fdeps, rg, rho),
                                    CFExtractSelA(adeps, rg, rho))
  {
    var rf := FeatExtract(rg);
    var selP := CFExtractSelP(fdeps, rg, rho);
    var selA := CFExtractSelA(adeps, rg, rho);
    var depsF := FeatReduceDeps(fsupp, fdeps, adeps);

    // FResInRepo.
    forall e | e in rf
      ensures e.0 in repo && forall f | f in e.1 :: (e.0, f) in fsupp
    {
      var p :| p in rg && !p.name.FeatureName? && e == (p, FeatSelOf(rg, p));
      assert p in FeatReduceRepo(repo, fsupp) && p !in FeatPkgs(fsupp);
      forall f | f in e.1
        ensures (e.0, f) in fsupp
      {
        var q :| q in rg && q.name.FeatureName?
              && q.name.fbase == p.name && q.version == p.version && f == q.name.feat;
        FeaturesLemmas.FeatPkgDecode(repo, fsupp, q);
        assert Package(q.name.fbase, q.version) == p;
      }
    }

    // Root entry.
    assert (root, FeatSelOf(rg, root)) in rf;

    // Feature unification: the feature set is a function of the package.
    forall e1, e2 | e1 in rf && e2 in rf && e1.0 == e2.0
      ensures e1.1 == e2.1
    {
      var p1 :| p1 in rg && !p1.name.FeatureName? && e1 == (p1, FeatSelOf(rg, p1));
      var p2 :| p2 in rg && !p2.name.FeatureName? && e2 == (p2, FeatSelOf(rg, p2));
      assert p1 == p2;
    }

    // Granularity, inherited from the concurrent resolution.
    forall e1, e2 | e1 in rf && e2 in rf
        && e1.0.name == e2.0.name && e1.0.version != e2.0.version
      ensures g(e1.0.version) != g(e2.0.version)
    {
      assert e1.0 in rg && e2.0 in rg;
    }

    SelPFunctional(fsupp, fdeps, adeps, rg, rho);
    SelAFunctional(fsupp, fdeps, adeps, rg, rho);

    // Parameterised closure.
    forall pe, e | pe in rf && e in fdeps && e.0 == pe.0
      ensures exists v | v in e.1.versions ::
        ((e.0, e.1), v) in selP && CFSelected(rf, e.1, v)
    {
      assert pe.0 in rg;
      if e.1.feats == {} {
        assert (e.0, Dep(e.1.name, e.1.versions)) in FeatParamEdges(fdeps);
      }
      forall f | f in e.1.feats
        ensures (e.0, Dep(FeatureName(e.1.name, f), e.1.versions)) in depsF
      {
        assert (e.0, Dep(FeatureName(e.1.name, f), e.1.versions)) in FeatParamEdges(fdeps);
      }
      DepOccurrenceSatisfied(repo, fsupp, fdeps, adeps, rg, rho, e.0, e.1);
      var v :| v in e.1.versions && CFSelected(rf, e.1, v)
            && (e.1.feats == {} ==> Selected((e.0, Dep(e.1.name, e.1.versions)), v, rg, rho))
            && (forall f | f in e.1.feats ::
                  Selected((e.0, Dep(FeatureName(e.1.name, f), e.1.versions)), v, rg, rho));
      if e.1.feats == {} {
        assert ((e.0, e.1), v) in selP;
      } else {
        var f0 :| f0 in e.1.feats;
        assert ((e.0, e.1), v) in selP;
      }
    }

    // Additional closure.
    forall pe, a | pe in rf && a in adeps && a.0.0 == pe.0 && a.0.1 in pe.1
      ensures exists v | v in a.1.versions ::
        ((a.0, a.1), v) in selA && CFSelected(rf, a.1, v)
    {
      var p :| p in rg && !p.name.FeatureName? && pe == (p, FeatSelOf(rg, p));
      var q :| q in rg && q.name.FeatureName?
            && q.name.fbase == p.name && q.version == p.version && a.0.1 == q.name.feat;
      var src := Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version);
      assert q == src;
      if a.1.feats == {} {
        assert (src, Dep(a.1.name, a.1.versions)) in FeatAddEdges(adeps);
      }
      forall f | f in a.1.feats
        ensures (src, Dep(FeatureName(a.1.name, f), a.1.versions)) in depsF
      {
        assert (src, Dep(FeatureName(a.1.name, f), a.1.versions)) in FeatAddEdges(adeps);
      }
      DepOccurrenceSatisfied(repo, fsupp, fdeps, adeps, rg, rho, src, a.1);
      var v :| v in a.1.versions && CFSelected(rf, a.1, v)
            && (a.1.feats == {} ==> Selected((src, Dep(a.1.name, a.1.versions)), v, rg, rho))
            && (forall f | f in a.1.feats ::
                  Selected((src, Dep(FeatureName(a.1.name, f), a.1.versions)), v, rg, rho));
      if a.1.feats == {} {
        assert ((a.0, a.1), v) in selA;
      } else {
        var f0 :| f0 in a.1.feats;
        assert ((a.0, a.1), v) in selA;
      }
    }
  }

  // The repaired Theorem 5.2.2, end to end: from a core resolution of the
  // doubly-reduced instance, via Theorem 4.2.4, under feature coherence.
  lemma ConcFeatReductionSoundCoherent(repo: set<Package>, fsupp: SupportRel,
                                       fdeps: FDepRel, adeps: AddDepRel, g: GranFn,
                                       root: Package, r: set<Package>)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires WfAddDeps(repo, fsupp, adeps)
    requires WfSupp(repo, fsupp)
    requires WfAddOwners(fsupp, adeps)
    requires CFUniqueDeps(fdeps) && CFUniqueAdds(adeps) && CFAddNotSelf(adeps)
    requires CFNonempty(fdeps, adeps)
    requires root in repo
    requires ValidResolution(ConcFeatReduceRepo(repo, fsupp, fdeps, adeps, g),
                             ConcFeatReduceDeps(fsupp, fdeps, adeps, g), GPkg(root, g), r)
    requires FeatureCoherent(fdeps, adeps, ConcExtractRes(r, g),
                             ConcExtractRho(r, FeatReduceDeps(fsupp, fdeps, adeps), g))
    ensures ValidConcFeatResolution(repo, fsupp, fdeps, adeps, g, root,
              FeatExtract(ConcExtractRes(r, g)),
              CFExtractSelP(fdeps, ConcExtractRes(r, g),
                            ConcExtractRho(r, FeatReduceDeps(fsupp, fdeps, adeps), g)),
              CFExtractSelA(adeps, ConcExtractRes(r, g),
                            ConcExtractRho(r, FeatReduceDeps(fsupp, fdeps, adeps), g)))
  {
    var depsF := FeatReduceDeps(fsupp, fdeps, adeps);
    var repoF := FeatReduceRepo(repo, fsupp);
    FeatDepsWf(repo, fsupp, fdeps, adeps);
    FeatDepsUnique(repo, fsupp, fdeps, adeps);
    FeatDepsNonempty(fsupp, fdeps, adeps);
    ConcurrentLemmas.ConcReductionSound(repoF, depsF, g, root, r);
    var rg := ConcExtractRes(r, g);
    var rho := ConcExtractRho(r, depsF, g);
    forall pr | pr in rho
      ensures pr.1 in rg
    {
      ParentInRg(r, depsF, g, pr);
    }
    ConcFeatExtractSound(repo, fsupp, fdeps, adeps, g, root, rg, rho);
  }

  // Feature coherence holds trivially when no dependency requires more
  // than one feature — so the repaired theorem subsumes that whole
  // syntactic class of instances.
  lemma CoherentWhenSingleFeature(fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                                  rg: set<Package>, rho: ParentRel)
    requires ParentClosure(FeatReduceDeps(fsupp, fdeps, adeps), rg, rho)
    requires forall pr | pr in rho :: pr.1 in rg
    requires forall e | e in fdeps :: |e.1.feats| <= 1
    requires forall a | a in adeps :: |a.1.feats| <= 1
    ensures FeatureCoherent(fdeps, adeps, rg, rho)
  {
    forall e, f1, f2, v1, v2 |
      e in fdeps && f1 in e.1.feats && f2 in e.1.feats
      && v1 in e.1.versions && v2 in e.1.versions
      && Selected((e.0, Dep(FeatureName(e.1.name, f1), e.1.versions)), v1, rg, rho)
      && Selected((e.0, Dep(FeatureName(e.1.name, f2), e.1.versions)), v2, rg, rho)
      ensures v1 == v2
    {
      if f1 != f2 {
        ConcurrentLemmas.SubsetCard({f1, f2}, e.1.feats);
        assert false;
      }
      var ed := (e.0, Dep(FeatureName(e.1.name, f1), e.1.versions));
      assert ed in FeatParamEdges(fdeps);
      assert ed.0 in rg;
    }
    forall a, f1, f2, v1, v2 |
      a in adeps && f1 in a.1.feats && f2 in a.1.feats
      && v1 in a.1.versions && v2 in a.1.versions
      && Selected((Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                   Dep(FeatureName(a.1.name, f1), a.1.versions)), v1, rg, rho)
      && Selected((Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                   Dep(FeatureName(a.1.name, f2), a.1.versions)), v2, rg, rho)
      ensures v1 == v2
    {
      if f1 != f2 {
        ConcurrentLemmas.SubsetCard({f1, f2}, a.1.feats);
        assert false;
      }
      var ed := (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                 Dep(FeatureName(a.1.name, f1), a.1.versions));
      assert ed in FeatAddEdges(adeps);
      assert ed.0 in rg;
    }
  }

  // Theorem 5.2.3 (Completeness of the composition).
  lemma ConcFeatComplete(repo: set<Package>, fsupp: SupportRel, fdeps: FDepRel, adeps: AddDepRel,
                         g: GranFn, root: Package, rf: FRes, selP: ParamSel, selA: AddSel)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires WfFDeps(repo, fsupp, fdeps)
    requires WfAddDeps(repo, fsupp, adeps)
    requires WfSupp(repo, fsupp)
    requires WfAddOwners(fsupp, adeps)
    requires CFUniqueDeps(fdeps) && CFUniqueAdds(adeps) && CFAddNotSelf(adeps)
    requires CFNonempty(fdeps, adeps)
    requires root in repo
    requires ValidConcFeatResolution(repo, fsupp, fdeps, adeps, g, root, rf, selP, selA)
    ensures ValidResolution(ConcFeatReduceRepo(repo, fsupp, fdeps, adeps, g),
                            ConcFeatReduceDeps(fsupp, fdeps, adeps, g),
                            GPkg(root, g),
                            ConcBuildCore(FeatBuildCore(rf),
                                          ConcFeatRho(rf, selP, selA, fdeps, adeps),
                                          FeatReduceDeps(fsupp, fdeps, adeps), g))
  {
    FeatDepsWf(repo, fsupp, fdeps, adeps);
    FeatDepsUnique(repo, fsupp, fdeps, adeps);
    FeatDepsNonempty(fsupp, fdeps, adeps);
    Bridge(repo, fsupp, fdeps, adeps, g, root, rf, selP, selA);
    ConcurrentLemmas.ConcReductionComplete(FeatReduceRepo(repo, fsupp),
                                           FeatReduceDeps(fsupp, fdeps, adeps), g, root,
                                           FeatBuildCore(rf),
                                           ConcFeatRho(rf, selP, selA, fdeps, adeps));
  }
}
