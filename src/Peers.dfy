// Peers.dfy — The Peer Package Calculus (§4.3).
//
// Definitions 4.3.1–4.3.3 of the paper, modelling npm's
// --legacy-peer-deps behaviour: a peer dependency (c, (m, S_peer)) ∈ B
// says that a parent of c may only depend on the peer name m with a
// version in S_peer. The constraint binds only when the parent actually
// depends on m (legacy behaviour); the selected version must then satisfy
// both the parent's and the peer's constraints.
//
// The reduction modifies the concurrent reduction (Definition 4.2.3) to
// give every dependency an intermediate package ⟨n, v, m⟩ carrying *full*
// versions rather than granularities — so an exact peer version can be
// pinned as the intersection of constraints — and adds, for each peer
// link, (ii)(A) extra intermediate versions covering the peer's version
// set and (ii)(B) a dependency from the child's intermediate selection to
// the peer's intermediate, restricted to the peer's version set.
//
// Theorems 4.3.4 and 4.3.5 are proved in lemmas/PeersLemmas.dfy. The same
// side conditions as §4.2 apply (UniqueDepPerName, NonemptyDeps).

include "Core.dfy"
include "Concurrent.dfy"

module Peers {
  import opened Core
  import opened Concurrent

  // Definition 4.3.1: peer dependencies B ⊆ P × (N × ℘(V)).
  type PeerRel = set<(Package, Dep)>

  // Definition 4.3.2(b): if c ∈ r has a peer dependency on m and c's
  // parent depends on m, the version resolved for the parent must satisfy
  // both constraints (and be witnessed by ρ).
  predicate PeerSatisfaction(deps: DepRel, peers: PeerRel, r: set<Package>, rho: ParentRel) {
    forall pe, e |
      pe in peers && pe.0 in r
      && e in deps && (pe.0, e.0) in rho && e.1.name == pe.1.name ::
      exists u | u in e.1.versions ::
        u in pe.1.versions && Selected(e, u, r, rho)
  }

  // Definition 4.3.2: (r, ρ) ∈ S_B(D, B, root, g).
  predicate ValidPeerResolution(repo: set<Package>, deps: DepRel, peers: PeerRel,
                                g: GranFn, root: Package,
                                r: set<Package>, rho: ParentRel) {
    ValidConcurrentResolution(repo, deps, g, root, r, rho)
    && PeerSatisfaction(deps, peers, r, rho)
  }

  // Referenced peer packages exist (Definition 3.1.2's side condition,
  // applied to B).
  predicate WfPeers(repo: set<Package>, peers: PeerRel) {
    forall pe | pe in peers ::
      pe.0 in repo && forall u | u in pe.1.versions :: Package(pe.1.name, u) in repo
  }

  // A peer link: parent dependency ec reaches child pe.0, which declares
  // peer dependency pe.1, and the same parent also depends on the peer
  // name via em (legacy behaviour: the peer is only constrained when the
  // parent depends on it).
  predicate PeerLink(deps: DepRel, peers: PeerRel,
                     ec: (Package, Dep), pe: (Package, Dep), em: (Package, Dep)) {
    ec in deps && pe in peers && em in deps
    && pe.0.name == ec.1.name && pe.0.version in ec.1.versions
    && em.0 == ec.0 && em.1.name == pe.1.name
  }

  // ---------------------------------------------------------------------
  // The reduction to the core (Definition 4.3.3).
  // ---------------------------------------------------------------------

  // (a) + (b)(i)(A): every dependency's intermediate carries full versions.
  function PeerIntBase(deps: DepRel): set<Package> {
    set e, u | e in deps && u in e.1.versions :: Package(IName(e), u)
  }

  // (b)(ii)(A): peer links extend the peer-name intermediate with the
  // peer's version set.
  function PeerIntExt(deps: DepRel, peers: PeerRel): set<Package> {
    set ec, pe, em, u | ec in deps && pe in peers && em in deps
      && PeerLink(deps, peers, ec, pe, em) && u in pe.1.versions ::
      Package(IName(em), u)
  }

  function PeerReduceRepo(repo: set<Package>, deps: DepRel, peers: PeerRel, g: GranFn): set<Package> {
    ConcGranRepo(repo, g) + PeerIntBase(deps) + PeerIntExt(deps, peers)
  }

  // (b)(i)(B): from the depender to its intermediate, over the full
  // version set.
  function PeerBEdges(deps: DepRel, g: GranFn): DepRel {
    set e | e in deps :: (GPkg(e.0, g), Dep(IName(e), e.1.versions))
  }

  // (b)(i)(A): each intermediate version pins the exact granular dependee.
  function PeerAEdgesBase(deps: DepRel, g: GranFn): DepRel {
    set e, u | e in deps && u in e.1.versions ::
      (Package(IName(e), u), Dep(GranularName(e.1.name, g(u)), {u}))
  }

  // (b)(ii)(A): likewise for the peer-extended intermediate versions.
  function PeerAEdgesExt(deps: DepRel, peers: PeerRel, g: GranFn): DepRel {
    set ec, pe, em, u | ec in deps && pe in peers && em in deps
      && PeerLink(deps, peers, ec, pe, em) && u in pe.1.versions ::
      (Package(IName(em), u), Dep(GranularName(em.1.name, g(u)), {u}))
  }

  // (b)(ii)(B): selecting the child at the peer-declaring version forces
  // the peer intermediate into the peer's version set.
  function PeerPeerEdges(deps: DepRel, peers: PeerRel): DepRel {
    set ec, pe, em | ec in deps && pe in peers && em in deps
      && PeerLink(deps, peers, ec, pe, em) ::
      (Package(IName(ec), pe.0.version), Dep(IName(em), pe.1.versions))
  }

  function PeerReduceDeps(deps: DepRel, peers: PeerRel, g: GranFn): DepRel {
    PeerBEdges(deps, g) + PeerAEdgesBase(deps, g)
    + PeerAEdgesExt(deps, peers, g) + PeerPeerEdges(deps, peers)
  }

  // ---------------------------------------------------------------------
  // The constructions of Theorems 4.3.4 and 4.3.5.
  // ---------------------------------------------------------------------

  function PkgVersions(r: set<Package>): set<Version> {
    set q | q in r :: q.version
  }

  // Theorem 4.3.4: the resolution is extracted exactly as in Theorem 4.2.4
  // (ConcExtractRes); the parent relation reads the selected child version
  // directly off the full-version intermediate.
  function PeerExtractRho(r: set<Package>, deps: DepRel, g: GranFn): ParentRel {
    set e, u | e in deps && u in PkgVersions(r)
      && GPkg(e.0, g) in r
      && Package(IName(e), u) in r
      :: (Package(e.1.name, u), e.0)
  }

  // Theorem 4.3.5: granular images plus, for each dependency of a selected
  // package, the intermediate at the ρ-selected child's version.
  function PeerIntChoice(rg: set<Package>, rho: ParentRel, deps: DepRel): set<Package> {
    set e, u | e in deps && e.0 in rg && u in e.1.versions && Selected(e, u, rg, rho) ::
      Package(IName(e), u)
  }

  function PeerBuildCore(rg: set<Package>, rho: ParentRel, deps: DepRel, g: GranFn): set<Package> {
    ConcGranImage(rg, g) + PeerIntChoice(rg, rho, deps)
  }
}
