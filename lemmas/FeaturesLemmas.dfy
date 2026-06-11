// FeaturesLemmas.dfy — Proofs for §4.4.
//
//   Theorem 4.4.5 (Soundness):   a core resolution of the feature-reduced
//     instance yields a feature resolution: a package's selected features
//     are those whose feature packages accompany it, and the base edges
//     ⟨n, f⟩ → (n, {v}) plus version uniqueness align all feature packages
//     with their base (this is feature unification).
//   Theorem 4.4.6 (Completeness): a feature resolution yields a core
//     resolution of the reduced instance.

include "../src/Features.dfy"

module FeaturesLemmas {
  import opened Core
  import opened Features

  // A feature package in the reduced repository decodes to a support entry.
  lemma FeatPkgDecode(repo: set<Package>, fsupp: SupportRel, q: Package)
    requires forall p | p in repo :: !p.name.FeatureName?
    requires q in FeatReduceRepo(repo, fsupp)
    requires q.name.FeatureName?
    ensures (Package(q.name.fbase, q.version), q.name.feat) in fsupp
  {
    assert q !in repo;
    var s :| s in fsupp && q == Package(FeatureName(s.0.name, s.1), s.0.version);
    assert s.0 == Package(q.name.fbase, q.version);
  }

  // A feature package selected in the core resolution forces its base
  // package, at the same version, into the resolution.
  lemma FeatPkgForcesBase(repo: set<Package>, fsupp: SupportRel,
                          fdeps: FDepRel, adeps: AddDepRel,
                          r: set<Package>, q: Package)
    requires forall p | p in repo :: !p.name.FeatureName?
    requires r <= FeatReduceRepo(repo, fsupp)
    requires DepClosure(FeatReduceDeps(fsupp, fdeps, adeps), r)
    requires q in r && q.name.FeatureName?
    ensures Package(q.name.fbase, q.version) in r
  {
    FeatPkgDecode(repo, fsupp, q);
    var s := (Package(q.name.fbase, q.version), q.name.feat);
    var bEdge := (q, Dep(q.name.fbase, {q.version}));
    assert bEdge == (Package(FeatureName(s.0.name, s.1), s.0.version), Dep(s.0.name, {s.0.version}));
    assert bEdge in FeatBaseEdges(fsupp);
    var w :| w in bEdge.1.versions && Package(bEdge.1.name, w) in r;
    assert w == q.version;
  }

  // Core closure of the reduced edges for a dependency target d implies
  // the feature-calculus satisfaction of d in the extracted resolution.
  @IsolateAssertions
  lemma EdgesGiveSatisfaction(repo: set<Package>, fsupp: SupportRel,
                              fdeps: FDepRel, adeps: AddDepRel,
                              r: set<Package>, src: Package, d: FDep)
    requires forall p | p in repo :: !p.name.FeatureName?
    requires !d.name.FeatureName?
    requires r <= FeatReduceRepo(repo, fsupp)
    requires DepClosure(FeatReduceDeps(fsupp, fdeps, adeps), r)
    requires VersionUniqueness(r)
    requires src in r
    requires d.feats == {} ==> (src, Dep(d.name, d.versions)) in FeatReduceDeps(fsupp, fdeps, adeps)
    requires forall f | f in d.feats ::
      (src, Dep(FeatureName(d.name, f), d.versions)) in FeatReduceDeps(fsupp, fdeps, adeps)
    ensures FDepSatisfied(FeatExtract(r), d)
  {
    if d.feats == {} {
      var u :| u in d.versions && Package(d.name, u) in r;
      var q := (Package(d.name, u), FeatSelOf(r, Package(d.name, u)));
      assert q in FeatExtract(r);
      assert q.0.name == d.name && q.0.version in d.versions && d.feats <= q.1;
    } else {
      var f0 :| f0 in d.feats;
      var u0 :| u0 in d.versions && Package(FeatureName(d.name, f0), u0) in r;
      FeatPkgForcesBase(repo, fsupp, fdeps, adeps, r, Package(FeatureName(d.name, f0), u0));
      assert Package(d.name, u0) in r;
      var base := Package(d.name, u0);
      var q := (base, FeatSelOf(r, base));
      assert q in FeatExtract(r);
      // Every required feature's package sits at the same version u0.
      forall f | f in d.feats
        ensures f in q.1
      {
        var uf :| uf in d.versions && Package(FeatureName(d.name, f), uf) in r;
        FeatPkgForcesBase(repo, fsupp, fdeps, adeps, r, Package(FeatureName(d.name, f), uf));
        assert Package(d.name, uf) in r;
        assert uf == u0;  // version uniqueness on the base name
        assert Package(FeatureName(d.name, f), u0) in r;
      }
      assert q.0.name == d.name && q.0.version in d.versions && d.feats <= q.1;
    }
  }

  // Theorem 4.4.5.
  @IsolateAssertions
  lemma FeatReductionSound(repo: set<Package>, fsupp: SupportRel,
                           fdeps: FDepRel, adeps: AddDepRel,
                           root: Package, r: set<Package>)
    requires WfFDeps(repo, fsupp, fdeps)
    requires WfAddDeps(repo, fsupp, adeps)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires forall s | s in fsupp :: s.0 in repo
    requires root in repo
    requires ValidResolution(FeatReduceRepo(repo, fsupp),
                             FeatReduceDeps(fsupp, fdeps, adeps), root, r)
    ensures ValidFeatureResolution(repo, fsupp, fdeps, adeps, root, FeatExtract(r))
  {
    var rf := FeatExtract(r);
    var rdeps := FeatReduceDeps(fsupp, fdeps, adeps);

    // FResInRepo: entries are existing packages with supported features.
    forall e | e in rf
      ensures e.0 in repo && forall f | f in e.1 :: (e.0, f) in fsupp
    {
      var p :| p in r && !p.name.FeatureName? && e == (p, FeatSelOf(r, p));
      assert p in FeatReduceRepo(repo, fsupp) && p !in FeatPkgs(fsupp);
      forall f | f in e.1
        ensures (e.0, f) in fsupp
      {
        var q :| q in r && q.name.FeatureName?
              && q.name.fbase == p.name && q.version == p.version && f == q.name.feat;
        FeatPkgDecode(repo, fsupp, q);
        assert Package(q.name.fbase, q.version) == p;
      }
    }

    // Root entry.
    assert (root, FeatSelOf(r, root)) in rf;

    // Parameterised dependency closure.
    forall pe, e | pe in rf && e in fdeps && e.0 == pe.0
      ensures FDepSatisfied(rf, e.1)
    {
      assert pe.0 in r;
      if e.1.feats == {} {
        assert (e.0, Dep(e.1.name, e.1.versions)) in FeatParamEdges(fdeps);
      }
      forall f | f in e.1.feats
        ensures (e.0, Dep(FeatureName(e.1.name, f), e.1.versions)) in rdeps
      {
        assert (e.0, Dep(FeatureName(e.1.name, f), e.1.versions)) in FeatParamEdges(fdeps);
      }
      EdgesGiveSatisfaction(repo, fsupp, fdeps, adeps, r, pe.0, e.1);
    }

    // Additional dependency closure.
    forall pe, a | pe in rf && a in adeps && a.0.0 == pe.0 && a.0.1 in pe.1
      ensures FDepSatisfied(rf, a.1)
    {
      // The owning feature package is in r at pe.0's version.
      var p :| p in r && !p.name.FeatureName? && pe == (p, FeatSelOf(r, p));
      var q :| q in r && q.name.FeatureName?
            && q.name.fbase == p.name && q.version == p.version && a.0.1 == q.name.feat;
      var src := Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version);
      assert q == src;
      if a.1.feats == {} {
        assert (src, Dep(a.1.name, a.1.versions)) in FeatAddEdges(adeps);
      }
      forall f | f in a.1.feats
        ensures (src, Dep(FeatureName(a.1.name, f), a.1.versions)) in rdeps
      {
        assert (src, Dep(FeatureName(a.1.name, f), a.1.versions)) in FeatAddEdges(adeps);
      }
      EdgesGiveSatisfaction(repo, fsupp, fdeps, adeps, r, src, a.1);
    }

    // Feature unification: the feature set is a function of the package.
    forall e1, e2 | e1 in rf && e2 in rf && e1.0 == e2.0
      ensures e1.1 == e2.1
    {
      var p1 :| p1 in r && !p1.name.FeatureName? && e1 == (p1, FeatSelOf(r, p1));
      var p2 :| p2 in r && !p2.name.FeatureName? && e2 == (p2, FeatSelOf(r, p2));
      assert p1 == p2;
    }

    // Version uniqueness, inherited from the core.
    forall e1, e2 | e1 in rf && e2 in rf && e1.0.name == e2.0.name
      ensures e1.0.version == e2.0.version
    {
      assert e1.0 in r && e2.0 in r;
    }
  }

  // FDepSatisfied provides the core witnesses for the reduced edges.
  lemma SatisfiedGivesPlainWitness(rf: FRes, d: FDep)
    requires FDepSatisfied(rf, d)
    ensures exists v :: v in d.versions && Package(d.name, v) in FeatBuildCore(rf)
  {
    var q :| q in rf && q.0.name == d.name && q.0.version in d.versions && d.feats <= q.1;
    assert q.0 in FeatBuildCore(rf);
    assert q.0 == Package(d.name, q.0.version);
  }

  lemma SatisfiedGivesFeatureWitness(rf: FRes, d: FDep, f: Feature)
    requires FDepSatisfied(rf, d)
    requires f in d.feats
    ensures exists v :: v in d.versions && Package(FeatureName(d.name, f), v) in FeatBuildCore(rf)
  {
    var q :| q in rf && q.0.name == d.name && q.0.version in d.versions && d.feats <= q.1;
    assert Package(FeatureName(q.0.name, f), q.0.version) in FeatBuildCore(rf);
  }

  // A feature package in the built core resolution decodes to an entry of
  // the feature resolution that enables that feature.
  lemma BuildFeatDecode(repo: set<Package>, rf: FRes, q: Package)
    requires forall e | e in rf :: e.0 in repo
    requires forall p | p in repo :: !p.name.FeatureName?
    requires q in FeatBuildCore(rf)
    requires q.name.FeatureName?
    ensures exists e | e in rf ::
      e.0 == Package(q.name.fbase, q.version) && q.name.feat in e.1
  {
    if q in (set e | e in rf :: e.0) {
      var e :| e in rf && q == e.0;
      assert false;
    }
    var e, f :| e in rf && f in e.1 && q == Package(FeatureName(e.0.name, f), e.0.version);
    assert e.0 == Package(q.name.fbase, q.version) && q.name.feat in e.1;
  }

  // Theorem 4.4.6.
  @IsolateAssertions
  lemma FeatReductionComplete(repo: set<Package>, fsupp: SupportRel,
                              fdeps: FDepRel, adeps: AddDepRel,
                              root: Package, rf: FRes)
    requires WfFDeps(repo, fsupp, fdeps)
    requires WfAddDeps(repo, fsupp, adeps)
    requires PlainFeatureInstance(repo, fsupp, fdeps, adeps)
    requires root in repo
    requires ValidFeatureResolution(repo, fsupp, fdeps, adeps, root, rf)
    ensures ValidResolution(FeatReduceRepo(repo, fsupp),
                            FeatReduceDeps(fsupp, fdeps, adeps), root, FeatBuildCore(rf))
  {
    var r := FeatBuildCore(rf);
    var basePart := set e | e in rf :: e.0;
    var featPart := set e, f | e in rf && f in e.1 ::
      Package(FeatureName(e.0.name, f), e.0.version);
    assert r == basePart + featPart;

    // r ⊆ reduced repo.
    forall q | q in r
      ensures q in FeatReduceRepo(repo, fsupp)
    {
      if q in basePart {
        var e :| e in rf && q == e.0;
        assert q in repo;
      } else {
        var e, f :| e in rf && f in e.1 && q == Package(FeatureName(e.0.name, f), e.0.version);
        assert (e.0, f) in fsupp;  // FResInRepo
        assert q in FeatPkgs(fsupp);
      }
    }

    // Root inclusion.
    var re :| re in rf && re.0 == root;
    assert root in basePart;

    // Version uniqueness.
    forall p, q | p in r && q in r && p.name == q.name
      ensures p.version == q.version
    {
      if p in basePart && q in basePart {
        var e1 :| e1 in rf && p == e1.0;
        var e2 :| e2 in rf && q == e2.0;
        assert e1.0.version == e2.0.version;  // FVersionUniqueness
      } else if p in featPart && q in featPart {
        var e1, f1 :| e1 in rf && f1 in e1.1 && p == Package(FeatureName(e1.0.name, f1), e1.0.version);
        var e2, f2 :| e2 in rf && f2 in e2.1 && q == Package(FeatureName(e2.0.name, f2), e2.0.version);
        assert e1.0.name == e2.0.name;
        assert e1.0.version == e2.0.version;  // FVersionUniqueness
      } else if p in basePart {
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

    // Dependency closure over the three groups of reduced edges.
    forall ed | ed in FeatReduceDeps(fsupp, fdeps, adeps) && ed.0 in r
      ensures exists v :: v in ed.1.versions && Package(ed.1.name, v) in r
    {
      if ed in FeatBaseEdges(fsupp) {
        // ⟨n, f⟩ → (n, {v}): the base accompanies its feature package.
        var s :| s in fsupp
              && ed == (Package(FeatureName(s.0.name, s.1), s.0.version), Dep(s.0.name, {s.0.version}));
        BuildFeatDecode(repo, rf, ed.0);
        var e :| e in rf && e.0 == Package(ed.0.name.fbase, ed.0.version) && ed.0.name.feat in e.1;
        assert e.0 in basePart;
        assert e.0 == Package(s.0.name, s.0.version);
        assert s.0.version in ed.1.versions && Package(ed.1.name, s.0.version) in r;
      } else if ed in FeatParamEdges(fdeps) {
        // The depender is a plain package, so it carries an rf entry.
        SourceEntry(repo, fsupp, rf, ed.0);
        var pe :| pe in rf && pe.0 == ed.0;
        if ed in (set e | e in fdeps && e.1.feats == {} :: (e.0, Dep(e.1.name, e.1.versions))) {
          var e :| e in fdeps && e.1.feats == {} && ed == (e.0, Dep(e.1.name, e.1.versions));
          assert FDepSatisfied(rf, e.1);  // ParamClosure
          SatisfiedGivesPlainWitness(rf, e.1);
        } else {
          var e, f :| e in fdeps && f in e.1.feats
                && ed == (e.0, Dep(FeatureName(e.1.name, f), e.1.versions));
          assert FDepSatisfied(rf, e.1);  // ParamClosure
          SatisfiedGivesFeatureWitness(rf, e.1, f);
        }
      } else {
        assert ed in FeatAddEdges(adeps);
        // The depender is a feature package ⟨p, f'⟩; decode it to an rf
        // entry of p that enables f', then apply additional closure.
        if ed in (set a | a in adeps && a.1.feats == {} ::
            (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version), Dep(a.1.name, a.1.versions))) {
          var a :| a in adeps && a.1.feats == {}
                && ed == (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version), Dep(a.1.name, a.1.versions));
          BuildFeatDecode(repo, rf, ed.0);
          var e :| e in rf && e.0 == Package(ed.0.name.fbase, ed.0.version) && ed.0.name.feat in e.1;
          assert e.0 == a.0.0 && a.0.1 in e.1;
          assert FDepSatisfied(rf, a.1);  // AddClosure
          SatisfiedGivesPlainWitness(rf, a.1);
        } else {
          var a, f :| a in adeps && f in a.1.feats
                && ed == (Package(FeatureName(a.0.0.name, a.0.1), a.0.0.version),
                          Dep(FeatureName(a.1.name, f), a.1.versions));
          BuildFeatDecode(repo, rf, ed.0);
          var e :| e in rf && e.0 == Package(ed.0.name.fbase, ed.0.version) && ed.0.name.feat in e.1;
          assert e.0 == a.0.0 && a.0.1 in e.1;
          assert FDepSatisfied(rf, a.1);  // AddClosure
          SatisfiedGivesFeatureWitness(rf, a.1, f);
        }
      }
    }
  }

  // A plain depender in the built resolution has an rf entry.
  lemma SourceEntry(repo: set<Package>, fsupp: SupportRel, rf: FRes, p: Package)
    requires forall e | e in rf :: e.0 in repo
    requires forall q | q in repo :: !q.name.FeatureName?
    requires !p.name.FeatureName?
    requires p in FeatBuildCore(rf)
    ensures exists e | e in rf :: e.0 == p
  {
    if p in (set e | e in rf :: e.0) {
      var e :| e in rf && p == e.0;
    } else {
      var e, f :| e in rf && f in e.1 && p == Package(FeatureName(e.0.name, f), e.0.version);
      assert false;
    }
  }
}
