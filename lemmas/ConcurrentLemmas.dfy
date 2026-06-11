// ConcurrentLemmas.dfy — Proofs for §4.2.
//
//   Theorem 4.2.4 (Soundness):   a core resolution of the reduced instance
//     yields a concurrent resolution and parent relation.
//   Theorem 4.2.5 (Completeness): a concurrent resolution yields a core
//     resolution of the reduced instance.
//   CoreEmulation*:              Definition 4.2.1's remark that g(v) = c
//     emulates the single-version core condition.
//
// Side conditions (declared in src/Concurrent.dfy): at most one dependency
// per (depender, dependee-name) pair, no empty version sets, and
// well-formed dependencies.

include "../src/Concurrent.dfy"

module ConcurrentLemmas {
  import opened Core
  import opened Concurrent

  lemma SubsetCard<T>(a: set<T>, b: set<T>)
    requires a <= b
    ensures |a| <= |b|
    decreases a
  {
    if a != {} {
      var x :| x in a;
      SubsetCard(a - {x}, b - {x});
    }
  }

  // In a non-split dependency every version shares one granularity.
  lemma SingletonGran(e: (Package, Dep), g: GranFn, u1: Version, u2: Version)
    requires !IsSplit(e, g)
    requires u1 in e.1.versions && u2 in e.1.versions
    ensures g(u1) == g(u2)
  {
    if g(u1) != g(u2) {
      assert {g(u1), g(u2)} <= Grans(e.1.versions, g);
      SubsetCard({g(u1), g(u2)}, Grans(e.1.versions, g));
      assert false;
    }
  }

  // Theorem 4.2.4.
  lemma ConcReductionSound(repo: set<Package>, deps: DepRel, g: GranFn,
                           root: Package, r: set<Package>)
    requires WfDeps(repo, deps)
    requires UniqueDepPerName(deps)
    requires NonemptyDeps(deps)
    requires root in repo
    requires ValidResolution(ConcReduceRepo(repo, deps, g), ConcReduceDeps(deps, g), GPkg(root, g), r)
    ensures ValidConcurrentResolution(repo, deps, g, root,
                                      ConcExtractRes(r, g), ConcExtractRho(r, deps, g))
  {
    var rg := ConcExtractRes(r, g);
    var rho := ConcExtractRho(r, deps, g);
    var rdeps := ConcReduceDeps(deps, g);

    // rg ⊆ repo.
    forall q | q in rg
      ensures q in repo
    {
      var p :| p in r && p.name.GranularName? && p.name.gran == g(p.version)
            && q == Package(p.name.gbase, p.version);
      assert p !in ConcIntRepo(deps, g);
      var p0 :| p0 in repo && p == GPkg(p0, g);
      assert q == p0;
    }

    // Root inclusion.
    assert GPkg(root, g) in r;
    assert root == Package(GPkg(root, g).name.gbase, GPkg(root, g).version);
    assert root in rg;

    // Version granularity, from core version uniqueness on granular names.
    forall p, q | p in rg && q in rg && p.name == q.name && p.version != q.version
      ensures g(p.version) != g(q.version)
    {
      if g(p.version) == g(q.version) {
        var p' :| p' in r && p'.name.GranularName? && p'.name.gran == g(p'.version)
              && p == Package(p'.name.gbase, p'.version);
        var q' :| q' in r && q'.name.GranularName? && q'.name.gran == g(q'.version)
              && q == Package(q'.name.gbase, q'.version);
        assert p'.name == GranularName(p.name, g(p.version));
        assert q'.name == GranularName(q.name, g(q.version));
        assert p'.version == q'.version;  // core uniqueness in r
        assert false;
      }
    }

    // Parent closure.
    forall e | e in deps && e.0 in rg
      ensures (exists v | v in e.1.versions :: Selected(e, v, rg, rho))
           && (forall v1, v2 | v1 in e.1.versions && v2 in e.1.versions
                 && Selected(e, v1, rg, rho) && Selected(e, v2, rg, rho) :: v1 == v2)
    {
      // e.0 ∈ rg gives GPkg(e.0, g) ∈ r.
      var p' :| p' in r && p'.name.GranularName? && p'.name.gran == g(p'.version)
            && e.0 == Package(p'.name.gbase, p'.version);
      assert p' == GPkg(e.0, g);

      if IsSplit(e, g) {
        // Existence: follow the B edge to the intermediate, then the A edge.
        var bEdge := (GPkg(e.0, g), Dep(IName(e), Grans(e.1.versions, g)));
        assert bEdge in ConcSplitBEdges(deps, g);
        var gam :| gam in Grans(e.1.versions, g) && Package(IName(e), gam) in r;
        var aEdge := (Package(IName(e), gam),
                      Dep(GranularName(e.1.name, gam), Bucket(e.1.versions, g, gam)));
        assert aEdge in ConcSplitAEdges(deps, g);
        var u :| u in Bucket(e.1.versions, g, gam)
              && Package(GranularName(e.1.name, gam), u) in r;
        assert g(u) == gam;
        assert Package(e.1.name, u) in rg;
        assert (Package(e.1.name, u), e.0) in ConcRhoSplit(r, deps, g);
        assert Selected(e, u, rg, rho);

        // Uniqueness: any selected child of e is reached via the unique
        // version of the intermediate and the unique version of the
        // granular dependee.
        forall v1, v2 | v1 in e.1.versions && v2 in e.1.versions
              && Selected(e, v1, rg, rho) && Selected(e, v2, rg, rho)
          ensures v1 == v2
        {
          var w1 := RhoChildVersionSplit(r, deps, g, e, v1);
          var w2 := RhoChildVersionSplit(r, deps, g, e, v2);
        }
      } else {
        // Existence: the single granularity's direct edge.
        var v0 :| v0 in e.1.versions;  // NonemptyDeps
        var gam := g(v0);
        var dEdge := (GPkg(e.0, g), Dep(GranularName(e.1.name, gam), e.1.versions));
        assert dEdge in ConcDirectEdges(deps, g);
        var u :| u in e.1.versions && Package(GranularName(e.1.name, gam), u) in r;
        SingletonGran(e, g, u, v0);
        assert g(u) == gam;
        assert Package(e.1.name, u) in rg;
        assert (Package(e.1.name, u), e.0) in ConcRhoDirect(r, deps, g);
        assert Selected(e, u, rg, rho);

        forall v1, v2 | v1 in e.1.versions && v2 in e.1.versions
              && Selected(e, v1, rg, rho) && Selected(e, v2, rg, rho)
          ensures v1 == v2
        {
          RhoChildVersionDirect(r, deps, g, e, v1);
          RhoChildVersionDirect(r, deps, g, e, v2);
          SingletonGran(e, g, v1, v2);
          assert Package(GranularName(e.1.name, g(v1)), v1) in r;
          assert Package(GranularName(e.1.name, g(v2)), v2) in r;
        }
      }
    }
  }

  // For a split dependency e, any ρ-pair for (e.1.name, e.0) pins the
  // child version to the unique intermediate/granular selection.
  lemma RhoChildVersionSplit(r: set<Package>, deps: DepRel, g: GranFn,
                             e: (Package, Dep), v: Version)
    returns (gam: Granularity)
    requires UniqueDepPerName(deps)
    requires VersionUniqueness(r)
    requires e in deps && IsSplit(e, g)
    requires (Package(e.1.name, v), e.0) in ConcExtractRho(r, deps, g)
    ensures gam in Grans(e.1.versions, g)
    ensures Package(IName(e), gam) in r
    ensures Package(GranularName(e.1.name, gam), v) in r
    ensures forall w | Package(GranularName(e.1.name, gam), w) in r :: w == v
  {
    if (Package(e.1.name, v), e.0) in ConcRhoSplit(r, deps, g) {
      var e', gam', u :| e' in deps && IsSplit(e', g)
        && gam' in Grans(e'.1.versions, g) && u in e'.1.versions
        && GPkg(e'.0, g) in r
        && Package(IName(e'), gam') in r
        && Package(GranularName(e'.1.name, gam'), u) in r
        && (Package(e'.1.name, u), e'.0) == (Package(e.1.name, v), e.0);
      assert e' == e;  // UniqueDepPerName via matching depender and name
      gam := gam';
    } else {
      // A direct pair would require !IsSplit(e) by UniqueDepPerName.
      var e', u :| e' in deps && !IsSplit(e', g)
        && u in e'.1.versions
        && GPkg(e'.0, g) in r
        && Package(GranularName(e'.1.name, g(u)), u) in r
        && (Package(e'.1.name, u), e'.0) == (Package(e.1.name, v), e.0);
      assert e' == e;
      assert false;
    }
  }

  // Likewise for direct dependencies.
  lemma RhoChildVersionDirect(r: set<Package>, deps: DepRel, g: GranFn,
                              e: (Package, Dep), v: Version)
    requires UniqueDepPerName(deps)
    requires e in deps && !IsSplit(e, g)
    requires (Package(e.1.name, v), e.0) in ConcExtractRho(r, deps, g)
    ensures v in e.1.versions
    ensures Package(GranularName(e.1.name, g(v)), v) in r
  {
    if (Package(e.1.name, v), e.0) in ConcRhoSplit(r, deps, g) {
      var e', gam', u :| e' in deps && IsSplit(e', g)
        && gam' in Grans(e'.1.versions, g) && u in e'.1.versions
        && GPkg(e'.0, g) in r
        && Package(IName(e'), gam') in r
        && Package(GranularName(e'.1.name, gam'), u) in r
        && (Package(e'.1.name, u), e'.0) == (Package(e.1.name, v), e.0);
      assert e' == e;
      assert false;
    } else {
      var e', u :| e' in deps && !IsSplit(e', g)
        && u in e'.1.versions
        && GPkg(e'.0, g) in r
        && Package(GranularName(e'.1.name, g(u)), u) in r
        && (Package(e'.1.name, u), e'.0) == (Package(e.1.name, v), e.0);
      assert e' == e;
    }
  }

  // Theorem 4.2.5.
  lemma ConcReductionComplete(repo: set<Package>, deps: DepRel, g: GranFn,
                              root: Package, rg: set<Package>, rho: ParentRel)
    requires WfDeps(repo, deps)
    requires UniqueDepPerName(deps)
    requires NonemptyDeps(deps)
    requires root in repo
    requires ValidConcurrentResolution(repo, deps, g, root, rg, rho)
    ensures ValidResolution(ConcReduceRepo(repo, deps, g), ConcReduceDeps(deps, g),
                            GPkg(root, g), ConcBuildCore(rg, rho, deps, g))
  {
    var r := ConcBuildCore(rg, rho, deps, g);

    // r ⊆ reduced repo.
    forall q | q in r
      ensures q in ConcReduceRepo(repo, deps, g)
    {
      if q in ConcGranImage(rg, g) {
        var p :| p in rg && q == GPkg(p, g);
        assert q in ConcGranRepo(repo, g);
      } else {
        var e, u :| e in deps && IsSplit(e, g) && e.0 in rg
          && u in e.1.versions && Selected(e, u, rg, rho)
          && q == Package(IName(e), g(u));
        assert g(u) in Grans(e.1.versions, g);
        assert q in ConcIntRepo(deps, g);
      }
    }

    // Version uniqueness.
    forall p, q | p in r && q in r && p.name == q.name
      ensures p.version == q.version
    {
      if p in ConcGranImage(rg, g) && q in ConcGranImage(rg, g) {
        var p0 :| p0 in rg && p == GPkg(p0, g);
        var q0 :| q0 in rg && q == GPkg(q0, g);
        assert p0.name == q0.name && g(p0.version) == g(q0.version);
        assert p0.version == q0.version;  // VersionGranularity
      } else if p in ConcIntChoice(rg, rho, deps, g) && q in ConcIntChoice(rg, rho, deps, g) {
        var e1, u1 :| e1 in deps && IsSplit(e1, g) && e1.0 in rg
          && u1 in e1.1.versions && Selected(e1, u1, rg, rho)
          && p == Package(IName(e1), g(u1));
        var e2, u2 :| e2 in deps && IsSplit(e2, g) && e2.0 in rg
          && u2 in e2.1.versions && Selected(e2, u2, rg, rho)
          && q == Package(IName(e2), g(u2));
        assert e1.0 == e2.0 && e1.1.name == e2.1.name;
        assert e1 == e2;  // UniqueDepPerName
        assert u1 == u2;  // ParentClosure uniqueness
      } else if p in ConcGranImage(rg, g) {
        var p0 :| p0 in rg && p == GPkg(p0, g);
        var e2, u2 :| e2 in deps && IsSplit(e2, g) && e2.0 in rg
          && u2 in e2.1.versions && Selected(e2, u2, rg, rho)
          && q == Package(IName(e2), g(u2));
        assert false;  // GranularName vs IntermediateName
      } else {
        var q0 :| q0 in rg && q == GPkg(q0, g);
        var e1, u1 :| e1 in deps && IsSplit(e1, g) && e1.0 in rg
          && u1 in e1.1.versions && Selected(e1, u1, rg, rho)
          && p == Package(IName(e1), g(u1));
        assert false;
      }
    }

    // Dependency closure over the three groups of reduced edges.
    forall ed | ed in ConcReduceDeps(deps, g) && ed.0 in r
      ensures exists v :: v in ed.1.versions && Package(ed.1.name, v) in r
    {
      if ed in ConcDirectEdges(deps, g) {
        var e, gam :| e in deps && !IsSplit(e, g) && gam in Grans(e.1.versions, g)
          && ed == (GPkg(e.0, g), Dep(GranularName(e.1.name, gam), e.1.versions));
        SourceIsGranular(rg, rho, deps, g, e.0, ed.0);
        var u :| u in e.1.versions && Selected(e, u, rg, rho);
        var v0 :| v0 in e.1.versions && gam == g(v0);
        SingletonGran(e, g, u, v0);
        assert GPkg(Package(e.1.name, u), g) == Package(GranularName(e.1.name, gam), u);
        assert Package(GranularName(e.1.name, gam), u) in ConcGranImage(rg, g);
        assert u in ed.1.versions && Package(ed.1.name, u) in r;
      } else if ed in ConcSplitBEdges(deps, g) {
        var e :| e in deps && IsSplit(e, g)
          && ed == (GPkg(e.0, g), Dep(IName(e), Grans(e.1.versions, g)));
        SourceIsGranular(rg, rho, deps, g, e.0, ed.0);
        var u :| u in e.1.versions && Selected(e, u, rg, rho);
        assert Package(IName(e), g(u)) in ConcIntChoice(rg, rho, deps, g);
        assert g(u) in ed.1.versions && Package(ed.1.name, g(u)) in r;
      } else {
        assert ed in ConcSplitAEdges(deps, g);
        var e, gam :| e in deps && IsSplit(e, g) && gam in Grans(e.1.versions, g)
          && ed == (Package(IName(e), gam),
                    Dep(GranularName(e.1.name, gam), Bucket(e.1.versions, g, gam)));
        // The intermediate is in r only at the granularity of the selected
        // child u; that child's granular image witnesses the A edge.
        assert ed.0 !in ConcGranImage(rg, g) by {
          if ed.0 in ConcGranImage(rg, g) {
            var p0 :| p0 in rg && ed.0 == GPkg(p0, g);
          }
        }
        var e', u :| e' in deps && IsSplit(e', g) && e'.0 in rg
          && u in e'.1.versions && Selected(e', u, rg, rho)
          && ed.0 == Package(IName(e'), g(u));
        assert e'.0 == e.0 && e'.1.name == e.1.name;
        assert e' == e;  // UniqueDepPerName
        assert gam == g(u);
        assert GPkg(Package(e.1.name, u), g) == Package(GranularName(e.1.name, gam), u);
        assert Package(GranularName(e.1.name, gam), u) in ConcGranImage(rg, g);
        assert u in Bucket(e.1.versions, g, gam);
        assert u in ed.1.versions && Package(ed.1.name, u) in r;
      }
    }

    assert GPkg(root, g) in ConcGranImage(rg, g);
  }

  // A granular package in the built core resolution comes from rg.
  lemma SourceIsGranular(rg: set<Package>, rho: ParentRel, deps: DepRel, g: GranFn,
                         p: Package, q: Package)
    requires q == GPkg(p, g)
    requires q in ConcBuildCore(rg, rho, deps, g)
    ensures p in rg
  {
    if q in ConcGranImage(rg, g) {
      var p0 :| p0 in rg && q == GPkg(p0, g);
      assert p0 == p;
    } else {
      var e, u :| e in deps && IsSplit(e, g) && e.0 in rg
        && u in e.1.versions && Selected(e, u, rg, rho)
        && q == Package(IName(e), g(u));
      assert false;  // GranularName vs IntermediateName
    }
  }

  // Definition 4.2.1's remark: a constant granularity function emulates
  // the single-version condition of the core calculus.
  function CanonicalRho(deps: DepRel, r: set<Package>): ParentRel {
    set e, v | e in deps && e.0 in r && v in e.1.versions && Package(e.1.name, v) in r ::
      (Package(e.1.name, v), e.0)
  }

  lemma CoreEmulationForward(repo: set<Package>, deps: DepRel, root: Package,
                             r: set<Package>, g: GranFn)
    requires forall v1, v2 :: g(v1) == g(v2)
    requires ValidResolution(repo, deps, root, r)
    ensures ValidConcurrentResolution(repo, deps, g, root, r, CanonicalRho(deps, r))
  {
    var rho := CanonicalRho(deps, r);
    forall e | e in deps && e.0 in r
      ensures (exists v | v in e.1.versions :: Selected(e, v, r, rho))
           && (forall v1, v2 | v1 in e.1.versions && v2 in e.1.versions
                 && Selected(e, v1, r, rho) && Selected(e, v2, r, rho) :: v1 == v2)
    {
      var v :| v in e.1.versions && Package(e.1.name, v) in r;
      assert Selected(e, v, r, rho);
    }
  }

  lemma CoreEmulationBackward(repo: set<Package>, deps: DepRel, root: Package,
                              r: set<Package>, rho: ParentRel, g: GranFn)
    requires forall v1, v2 :: g(v1) == g(v2)
    requires ValidConcurrentResolution(repo, deps, g, root, r, rho)
    ensures ValidResolution(repo, deps, root, r)
  {
    forall e | e in deps && e.0 in r
      ensures exists v :: v in e.1.versions && Package(e.1.name, v) in r
    {
      var v :| v in e.1.versions && Selected(e, v, r, rho);
    }
  }
}
