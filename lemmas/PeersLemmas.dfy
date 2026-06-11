// PeersLemmas.dfy — Proofs for §4.3.
//
//   Theorem 4.3.4 (Soundness):   a core resolution of the peer-reduced
//     instance yields a valid peer resolution and parent relation. The key
//     step for peer satisfaction: selecting the child at a peer-declaring
//     version activates the (ii)(B) edge into the peer's intermediate,
//     whose version uniqueness intersects the parent's constraint with the
//     peer's.
//   Theorem 4.3.5 (Completeness): a valid peer resolution yields a core
//     resolution of the peer-reduced instance; peer satisfaction provides
//     the witness for the (ii)(B) edges.

include "../src/Peers.dfy"

module PeersLemmas {
  import opened Core
  import opened Concurrent
  import opened Peers

  // The version of an intermediate selected next to its depender is in the
  // dependency's version set (the (i)(B) edge plus version uniqueness).
  lemma IntVersionInDep(deps: DepRel, peers: PeerRel, g: GranFn,
                        rdeps: DepRel, r: set<Package>, e: (Package, Dep), u: Version)
    requires rdeps == PeerReduceDeps(deps, peers, g)
    requires DepClosure(rdeps, r) && VersionUniqueness(r)
    requires e in deps
    requires GPkg(e.0, g) in r
    requires Package(IName(e), u) in r
    ensures u in e.1.versions
  {
    var bEdge := (GPkg(e.0, g), Dep(IName(e), e.1.versions));
    assert bEdge in PeerBEdges(deps, g);
    var u' :| u' in e.1.versions && Package(IName(e), u') in r;
    assert u == u';  // version uniqueness of the intermediate name
  }

  // A pair belongs to the extracted parent relation whenever its guards hold.
  lemma PairInRho(deps: DepRel, g: GranFn, r: set<Package>, e: (Package, Dep), u: Version)
    requires e in deps
    requires GPkg(e.0, g) in r
    requires Package(IName(e), u) in r
    ensures (Package(e.1.name, u), e.0) in PeerExtractRho(r, deps, g)
  {
    assert Package(IName(e), u).version == u;
    assert u in PkgVersions(r);
  }

  // An intermediate at version u pins the granular dependee at exactly u,
  // via its (A) edge — base or peer-extended.
  lemma IntSelectsChild(repo: set<Package>, deps: DepRel, peers: PeerRel, g: GranFn,
                        r: set<Package>, e: (Package, Dep), u: Version)
    requires UniqueDepPerName(deps)
    requires r <= PeerReduceRepo(repo, deps, peers, g)
    requires DepClosure(PeerReduceDeps(deps, peers, g), r)
    requires VersionUniqueness(r)
    requires e in deps && Package(IName(e), u) in r
    ensures Package(GranularName(e.1.name, g(u)), u) in r
    ensures Package(e.1.name, u) in ConcExtractRes(r, g)
  {
    var aEdge := (Package(IName(e), u), Dep(GranularName(e.1.name, g(u)), {u}));
    assert Package(IName(e), u) in PeerReduceRepo(repo, deps, peers, g);
    if Package(IName(e), u) in PeerIntBase(deps) {
      var e', u' :| e' in deps && u' in e'.1.versions
            && Package(IName(e'), u') == Package(IName(e), u);
      assert e' == e && u' == u;  // UniqueDepPerName
      assert aEdge in PeerAEdgesBase(deps, g);
    } else if Package(IName(e), u) in PeerIntExt(deps, peers) {
      var ec, pe, em, u' :| ec in deps && pe in peers && em in deps
            && PeerLink(deps, peers, ec, pe, em) && u' in pe.1.versions
            && Package(IName(em), u') == Package(IName(e), u);
      assert em == e && u' == u;  // UniqueDepPerName
      assert aEdge in PeerAEdgesExt(deps, peers, g);
    } else {
      var p0 :| p0 in ConcGranRepo(repo, g) && Package(IName(e), u) == p0;
      var p1 :| p1 in repo && p0 == GPkg(p1, g);
      assert false;
    }
    var w :| w in aEdge.1.versions && Package(aEdge.1.name, w) in r;
    assert w == u;
    var gp := Package(GranularName(e.1.name, g(u)), u);
    assert gp in r && gp.name.GranularName? && gp.name.gran == g(gp.version);
    assert Package(e.1.name, u) == Package(gp.name.gbase, gp.version);
  }

  // The extracted resolution stays within the original repository.
  lemma PeerExtractSubset(repo: set<Package>, deps: DepRel, peers: PeerRel, g: GranFn,
                          r: set<Package>)
    requires r <= PeerReduceRepo(repo, deps, peers, g)
    ensures ConcExtractRes(r, g) <= repo
  {
    forall q | q in ConcExtractRes(r, g)
      ensures q in repo
    {
      var p :| p in r && p.name.GranularName? && p.name.gran == g(p.version)
            && q == Package(p.name.gbase, p.version);
      assert p !in PeerIntBase(deps) && p !in PeerIntExt(deps, peers);
      var p0 :| p0 in repo && p == GPkg(p0, g);
      assert q == p0;
    }
  }

  // Version granularity, from core uniqueness on granular names.
  lemma PeerExtractGranularity(g: GranFn, r: set<Package>)
    requires VersionUniqueness(r)
    ensures VersionGranularity(g, ConcExtractRes(r, g))
  {
    var rg := ConcExtractRes(r, g);
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
  }

  // A selected child exists for one dependency of a selected depender.
  lemma PeerOneDepExists(repo: set<Package>, deps: DepRel, peers: PeerRel, g: GranFn,
                         r: set<Package>, e: (Package, Dep))
    requires UniqueDepPerName(deps)
    requires r <= PeerReduceRepo(repo, deps, peers, g)
    requires DepClosure(PeerReduceDeps(deps, peers, g), r)
    requires VersionUniqueness(r)
    requires e in deps && e.0 in ConcExtractRes(r, g)
    ensures exists v | v in e.1.versions ::
      Selected(e, v, ConcExtractRes(r, g), PeerExtractRho(r, deps, g))
  {
    var rg := ConcExtractRes(r, g);
    var rho := PeerExtractRho(r, deps, g);
    var p' :| p' in r && p'.name.GranularName? && p'.name.gran == g(p'.version)
          && e.0 == Package(p'.name.gbase, p'.version);
    assert p' == GPkg(e.0, g);
    var bEdge := (GPkg(e.0, g), Dep(IName(e), e.1.versions));
    assert bEdge in PeerBEdges(deps, g);
    var u :| u in e.1.versions && Package(IName(e), u) in r;
    IntSelectsChild(repo, deps, peers, g, r, e, u);
    PairInRho(deps, g, r, e, u);
    assert Selected(e, u, rg, rho);
  }

  // The selected child of one dependency is unique.
  lemma PeerOneDepUnique(deps: DepRel, g: GranFn, r: set<Package>,
                         e: (Package, Dep), v1: Version, v2: Version)
    requires UniqueDepPerName(deps)
    requires VersionUniqueness(r)
    requires e in deps
    requires v1 in e.1.versions && v2 in e.1.versions
    requires Selected(e, v1, ConcExtractRes(r, g), PeerExtractRho(r, deps, g))
    requires Selected(e, v2, ConcExtractRes(r, g), PeerExtractRho(r, deps, g))
    ensures v1 == v2
  {
    RhoPinsIntermediate(deps, g, r, e, v1);
    RhoPinsIntermediate(deps, g, r, e, v2);
    assert Package(IName(e), v1).name == Package(IName(e), v2).name;
  }

  // Parent closure of the extracted resolution and parent relation.
  @IsolateAssertions
  lemma PeerParentClosure(repo: set<Package>, deps: DepRel, peers: PeerRel, g: GranFn,
                          r: set<Package>)
    requires UniqueDepPerName(deps)
    requires r <= PeerReduceRepo(repo, deps, peers, g)
    requires DepClosure(PeerReduceDeps(deps, peers, g), r)
    requires VersionUniqueness(r)
    ensures ParentClosure(deps, ConcExtractRes(r, g), PeerExtractRho(r, deps, g))
  {
    hide *;
    reveal ParentClosure;
    var rg := ConcExtractRes(r, g);
    var rho := PeerExtractRho(r, deps, g);
    forall e | e in deps && e.0 in rg
      ensures (exists v | v in e.1.versions :: Selected(e, v, rg, rho))
           && (forall v1, v2 | v1 in e.1.versions && v2 in e.1.versions
                 && Selected(e, v1, rg, rho) && Selected(e, v2, rg, rho) :: v1 == v2)
    {
      PeerOneDepExists(repo, deps, peers, g, r, e);
      forall v1, v2 | v1 in e.1.versions && v2 in e.1.versions
            && Selected(e, v1, rg, rho) && Selected(e, v2, rg, rho)
        ensures v1 == v2
      {
        PeerOneDepUnique(deps, g, r, e, v1, v2);
      }
    }
  }

  // Peer satisfaction of the extracted resolution and parent relation.
  lemma PeerSatisfactionHolds(repo: set<Package>, deps: DepRel, peers: PeerRel, g: GranFn,
                              r: set<Package>)
    requires UniqueDepPerName(deps)
    requires r <= PeerReduceRepo(repo, deps, peers, g)
    requires DepClosure(PeerReduceDeps(deps, peers, g), r)
    requires VersionUniqueness(r)
    ensures PeerSatisfaction(deps, peers, ConcExtractRes(r, g), PeerExtractRho(r, deps, g))
  {
    var rg := ConcExtractRes(r, g);
    var rho := PeerExtractRho(r, deps, g);
    var rdeps := PeerReduceDeps(deps, peers, g);
    forall pe, em | pe in peers && pe.0 in rg
          && em in deps && (pe.0, em.0) in rho && em.1.name == pe.1.name
      ensures exists u | u in em.1.versions ::
        u in pe.1.versions && Selected(em, u, rg, rho)
    {
      // Decode the ρ pair: pe.0 was selected as the child of some
      // dependency ec of em.0, via the intermediate at version pe.0.version.
      var ec, w :| ec in deps && w in PkgVersions(r)
            && GPkg(ec.0, g) in r && Package(IName(ec), w) in r
            && (Package(ec.1.name, w), ec.0) == (pe.0, em.0);
      assert ec.1.name == pe.0.name && w == pe.0.version && ec.0 == em.0;
      IntVersionInDep(deps, peers, g, rdeps, r, ec, w);
      assert PeerLink(deps, peers, ec, pe, em);

      // The (ii)(B) edge forces the peer intermediate into pe.1.versions ...
      var pEdge := (Package(IName(ec), pe.0.version), Dep(IName(em), pe.1.versions));
      assert pEdge in PeerPeerEdges(deps, peers);
      var u :| u in pe.1.versions && Package(IName(em), u) in r;
      // ... and the parent's own (i)(B) edge intersects with em's versions.
      IntVersionInDep(deps, peers, g, rdeps, r, em, u);
      // GPkg(em.0, g) ∈ r since em.0 == ec.0.
      assert GPkg(em.0, g) == GPkg(ec.0, g);
      IntSelectsChild(repo, deps, peers, g, r, em, u);
      PairInRho(deps, g, r, em, u);
      assert Selected(em, u, rg, rho);
    }
  }

  // Theorem 4.3.4.
  lemma PeerReductionSound(repo: set<Package>, deps: DepRel, peers: PeerRel, g: GranFn,
                           root: Package, r: set<Package>)
    requires WfDeps(repo, deps)
    requires WfPeers(repo, peers)
    requires UniqueDepPerName(deps)
    requires NonemptyDeps(deps)
    requires root in repo
    requires ValidResolution(PeerReduceRepo(repo, deps, peers, g),
                             PeerReduceDeps(deps, peers, g), GPkg(root, g), r)
    ensures ValidPeerResolution(repo, deps, peers, g, root,
                                ConcExtractRes(r, g), PeerExtractRho(r, deps, g))
  {
    PeerExtractSubset(repo, deps, peers, g, r);
    PeerExtractGranularity(g, r);
    PeerParentClosure(repo, deps, peers, g, r);
    PeerSatisfactionHolds(repo, deps, peers, g, r);
    assert root == Package(GPkg(root, g).name.gbase, GPkg(root, g).version);
    assert root in ConcExtractRes(r, g);
  }

  // A ρ pair for dependency e pins the intermediate of e at the child's
  // version, so two selected children coincide by version uniqueness.
  lemma RhoPinsIntermediate(deps: DepRel, g: GranFn, r: set<Package>,
                            e: (Package, Dep), v: Version)
    requires UniqueDepPerName(deps)
    requires e in deps
    requires (Package(e.1.name, v), e.0) in PeerExtractRho(r, deps, g)
    ensures Package(IName(e), v) in r
  {
    var e', u :| e' in deps && u in PkgVersions(r)
          && GPkg(e'.0, g) in r && Package(IName(e'), u) in r
          && (Package(e'.1.name, u), e'.0) == (Package(e.1.name, v), e.0);
    assert e' == e;  // UniqueDepPerName
  }

  // Theorem 4.3.5.
  lemma PeerReductionComplete(repo: set<Package>, deps: DepRel, peers: PeerRel, g: GranFn,
                              root: Package, rg: set<Package>, rho: ParentRel)
    requires WfDeps(repo, deps)
    requires WfPeers(repo, peers)
    requires UniqueDepPerName(deps)
    requires NonemptyDeps(deps)
    requires root in repo
    requires ValidPeerResolution(repo, deps, peers, g, root, rg, rho)
    ensures ValidResolution(PeerReduceRepo(repo, deps, peers, g),
                            PeerReduceDeps(deps, peers, g),
                            GPkg(root, g), PeerBuildCore(rg, rho, deps, g))
  {
    var r := PeerBuildCore(rg, rho, deps, g);

    // r ⊆ reduced repo.
    forall q | q in r
      ensures q in PeerReduceRepo(repo, deps, peers, g)
    {
      if q in ConcGranImage(rg, g) {
        var p :| p in rg && q == GPkg(p, g);
        assert q in ConcGranRepo(repo, g);
      } else {
        var e, u :| e in deps && e.0 in rg && u in e.1.versions
              && Selected(e, u, rg, rho) && q == Package(IName(e), u);
        assert q in PeerIntBase(deps);
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
      } else if p in PeerIntChoice(rg, rho, deps) && q in PeerIntChoice(rg, rho, deps) {
        var e1, u1 :| e1 in deps && e1.0 in rg && u1 in e1.1.versions
              && Selected(e1, u1, rg, rho) && p == Package(IName(e1), u1);
        var e2, u2 :| e2 in deps && e2.0 in rg && u2 in e2.1.versions
              && Selected(e2, u2, rg, rho) && q == Package(IName(e2), u2);
        assert e1.0 == e2.0 && e1.1.name == e2.1.name;
        assert e1 == e2;   // UniqueDepPerName
        assert u1 == u2;   // ParentClosure uniqueness
      } else if p in ConcGranImage(rg, g) {
        var p0 :| p0 in rg && p == GPkg(p0, g);
        var e2, u2 :| e2 in deps && e2.0 in rg && u2 in e2.1.versions
              && Selected(e2, u2, rg, rho) && q == Package(IName(e2), u2);
        assert false;  // GranularName vs IntermediateName
      } else {
        var q0 :| q0 in rg && q == GPkg(q0, g);
        var e1, u1 :| e1 in deps && e1.0 in rg && u1 in e1.1.versions
              && Selected(e1, u1, rg, rho) && p == Package(IName(e1), u1);
        assert false;
      }
    }

    // An intermediate in the built resolution decodes to its dependency's
    // selected child.
    forall e, u | e in deps && Package(IName(e), u) in r
      ensures e.0 in rg && u in e.1.versions && Selected(e, u, rg, rho)
    {
      if Package(IName(e), u) in ConcGranImage(rg, g) {
        var p0 :| p0 in rg && Package(IName(e), u) == GPkg(p0, g);
        assert false;
      } else {
        var e', u' :| e' in deps && e'.0 in rg && u' in e'.1.versions
              && Selected(e', u', rg, rho) && Package(IName(e'), u') == Package(IName(e), u);
        assert e' == e && u' == u;  // UniqueDepPerName + version match
      }
    }

    // Dependency closure over the four groups of reduced edges.
    forall ed | ed in PeerReduceDeps(deps, peers, g) && ed.0 in r
      ensures exists v :: v in ed.1.versions && Package(ed.1.name, v) in r
    {
      if ed in PeerBEdges(deps, g) {
        var e :| e in deps && ed == (GPkg(e.0, g), Dep(IName(e), e.1.versions));
        PeerSourceIsGranular(rg, rho, deps, g, e.0, ed.0);
        var u :| u in e.1.versions && Selected(e, u, rg, rho);
        assert Package(IName(e), u) in PeerIntChoice(rg, rho, deps);
        assert u in ed.1.versions && Package(ed.1.name, u) in r;
      } else if ed in PeerAEdgesBase(deps, g) {
        var e, u :| e in deps && u in e.1.versions
              && ed == (Package(IName(e), u), Dep(GranularName(e.1.name, g(u)), {u}));
        assert Package(IName(e), u) in r;
        assert Selected(e, u, rg, rho);
        assert GPkg(Package(e.1.name, u), g) == Package(GranularName(e.1.name, g(u)), u);
        assert Package(GranularName(e.1.name, g(u)), u) in ConcGranImage(rg, g);
        assert u in ed.1.versions && Package(ed.1.name, u) in r;
      } else if ed in PeerAEdgesExt(deps, peers, g) {
        var ec, pe, em, u :| ec in deps && pe in peers && em in deps
              && PeerLink(deps, peers, ec, pe, em) && u in pe.1.versions
              && ed == (Package(IName(em), u), Dep(GranularName(em.1.name, g(u)), {u}));
        assert Package(IName(em), u) in r;
        assert Selected(em, u, rg, rho);
        assert GPkg(Package(em.1.name, u), g) == Package(GranularName(em.1.name, g(u)), u);
        assert Package(GranularName(em.1.name, g(u)), u) in ConcGranImage(rg, g);
        assert u in ed.1.versions && Package(ed.1.name, u) in r;
      } else {
        assert ed in PeerPeerEdges(deps, peers);
        var ec, pe, em :| ec in deps && pe in peers && em in deps
              && PeerLink(deps, peers, ec, pe, em)
              && ed == (Package(IName(ec), pe.0.version), Dep(IName(em), pe.1.versions));
        assert Package(IName(ec), pe.0.version) in r;
        assert Selected(ec, pe.0.version, rg, rho);
        // The selected child is exactly the peer-declaring package pe.0.
        assert Package(ec.1.name, pe.0.version) == pe.0;
        assert pe.0 in rg && (pe.0, ec.0) in rho;
        // Peer satisfaction provides the intersecting selection for em.
        var u :| u in em.1.versions && u in pe.1.versions && Selected(em, u, rg, rho);
        assert em.0 == ec.0 && ec.0 in rg;
        assert Package(IName(em), u) in PeerIntChoice(rg, rho, deps);
        assert u in ed.1.versions && Package(ed.1.name, u) in r;
      }
    }

    assert GPkg(root, g) in ConcGranImage(rg, g);
  }

  // A granular package in the built core resolution comes from rg.
  lemma PeerSourceIsGranular(rg: set<Package>, rho: ParentRel, deps: DepRel, g: GranFn,
                             p: Package, q: Package)
    requires q == GPkg(p, g)
    requires q in PeerBuildCore(rg, rho, deps, g)
    ensures p in rg
  {
    if q in ConcGranImage(rg, g) {
      var p0 :| p0 in rg && q == GPkg(p0, g);
      assert p0 == p;
    } else {
      var e, u :| e in deps && e.0 in rg && u in e.1.versions
            && Selected(e, u, rg, rho) && q == Package(IName(e), u);
      assert false;  // GranularName vs IntermediateName
    }
  }
}
