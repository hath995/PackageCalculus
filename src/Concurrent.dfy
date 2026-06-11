// Concurrent.dfy — The Concurrent Package Calculus (§4.2).
//
// Definitions 4.2.1–4.2.3 of the paper. Some package managers (Cargo, npm,
// Nix) allow multiple versions of a package name in a resolution; a
// granularity function g : V → G says which versions conflict (same
// granularity) and which may coexist (different granularities). Cargo's
// g extracts the semver major version; npm's is the identity; g = constant
// recovers the single-version core behaviour.
//
// A concurrent resolution carries a parent relation ρ ⊆ P × P (child,
// parent): each dependency of each selected package is satisfied by
// exactly one child, witnessed in ρ.
//
// The reduction pushes the granularity into the package name (granular
// packages ⟨n, γ⟩) so that core version uniqueness enforces version
// granularity, with intermediate packages ⟨n, v, m⟩ allowing one depender
// to reach multiple granular versions of a now-split name.
//
// Mechanisation notes:
//   - the paper names intermediates ⟨n, v, m⟩ — depender package plus
//     dependee *name* — which presumes at most one dependency per
//     (depender, dependee-name) pair; we make that explicit as the
//     UniqueDepPerName precondition;
//   - dependencies with empty version sets are unsatisfiable in the source
//     calculus but would vanish in the reduction, so NonemptyDeps is
//     required for the theorems.
//
// Theorems 4.2.4 and 4.2.5 are proved in lemmas/ConcurrentLemmas.dfy.

include "Core.dfy"

module Concurrent {
  import opened Core

  // Definition 4.2.1: the granularity function g : V → G.
  type Granularity = nat
  type GranFn = Version -> Granularity

  // The parent relation ρ ⊆ P × P, as (child, parent) pairs.
  type ParentRel = set<(Package, Package)>

  // Child (m, v) satisfies dependency e = (p, (m, S)) under (r, ρ).
  predicate Selected(e: (Package, Dep), v: Version, r: set<Package>, rho: ParentRel) {
    v in e.1.versions
    && Package(e.1.name, v) in r
    && (Package(e.1.name, v), e.0) in rho
  }

  // Definition 4.2.2(b): each dependency of each selected package has
  // exactly one child in the resolution, witnessed by ρ.
  predicate ParentClosure(deps: DepRel, r: set<Package>, rho: ParentRel) {
    forall e | e in deps && e.0 in r ::
      (exists v | v in e.1.versions :: Selected(e, v, r, rho))
      && (forall v1, v2 | v1 in e.1.versions && v2 in e.1.versions
            && Selected(e, v1, r, rho) && Selected(e, v2, r, rho) :: v1 == v2)
  }

  // Definition 4.2.2(c): distinct versions of a name must have distinct
  // granularities.
  predicate VersionGranularity(g: GranFn, r: set<Package>) {
    forall p, q | p in r && q in r && p.name == q.name && p.version != q.version ::
      g(p.version) != g(q.version)
  }

  // Definition 4.2.2: (r, ρ) ∈ S_γ(D, root, g).
  predicate ValidConcurrentResolution(repo: set<Package>, deps: DepRel, g: GranFn,
                                      root: Package, r: set<Package>, rho: ParentRel) {
    r <= repo
    && RootInclusion(root, r)
    && ParentClosure(deps, r, rho)
    && VersionGranularity(g, r)
  }

  // ---------------------------------------------------------------------
  // The reduction to the core (Definition 4.2.3).
  // ---------------------------------------------------------------------

  // Side conditions (see header).
  predicate UniqueDepPerName(deps: DepRel) {
    forall e1, e2 | e1 in deps && e2 in deps && e1.0 == e2.0 && e1.1.name == e2.1.name ::
      e1.1 == e2.1
  }

  predicate NonemptyDeps(deps: DepRel) {
    forall e | e in deps :: e.1.versions != {}
  }

  // Γ = {g(u) | u ∈ S}, and the bucket of versions at granularity γ.
  function Grans(s: set<Version>, g: GranFn): set<Granularity> {
    set v | v in s :: g(v)
  }

  function Bucket(s: set<Version>, g: GranFn, gam: Granularity): set<Version> {
    set v | v in s && g(v) == gam
  }

  // Definition 4.2.3(a)(i): the granular image ⟨n, g(v)⟩ of a package.
  function GPkg(p: Package, g: GranFn): Package {
    Package(GranularName(p.name, g(p.version)), p.version)
  }

  // The intermediate package name ⟨n, v, m⟩ of Definition 4.2.3(b)(ii).
  function IName(e: (Package, Dep)): Name {
    IntermediateName(e.0, e.1.name)
  }

  // Definition 4.2.3(b)(ii): a dependency is split when its version set
  // spans more than one granularity.
  predicate IsSplit(e: (Package, Dep), g: GranFn) {
    |Grans(e.1.versions, g)| > 1
  }

  // Definition 4.2.3(a): granular packages plus intermediates.
  function ConcGranRepo(repo: set<Package>, g: GranFn): set<Package> {
    set p | p in repo :: GPkg(p, g)
  }

  function ConcIntRepo(deps: DepRel, g: GranFn): set<Package> {
    set e, gam | e in deps && IsSplit(e, g) && gam in Grans(e.1.versions, g) ::
      Package(IName(e), gam)
  }

  function ConcReduceRepo(repo: set<Package>, deps: DepRel, g: GranFn): set<Package> {
    ConcGranRepo(repo, g) + ConcIntRepo(deps, g)
  }

  // Definition 4.2.3(b): direct edges for single-granularity dependencies;
  // split dependencies go via the intermediate (B), which fans out per
  // granularity (A).
  function ConcDirectEdges(deps: DepRel, g: GranFn): DepRel {
    set e, gam | e in deps && !IsSplit(e, g) && gam in Grans(e.1.versions, g) ::
      (GPkg(e.0, g), Dep(GranularName(e.1.name, gam), e.1.versions))
  }

  function ConcSplitBEdges(deps: DepRel, g: GranFn): DepRel {
    set e | e in deps && IsSplit(e, g) ::
      (GPkg(e.0, g), Dep(IName(e), Grans(e.1.versions, g)))
  }

  function ConcSplitAEdges(deps: DepRel, g: GranFn): DepRel {
    set e, gam | e in deps && IsSplit(e, g) && gam in Grans(e.1.versions, g) ::
      (Package(IName(e), gam), Dep(GranularName(e.1.name, gam), Bucket(e.1.versions, g, gam)))
  }

  function ConcReduceDeps(deps: DepRel, g: GranFn): DepRel {
    ConcDirectEdges(deps, g) + ConcSplitBEdges(deps, g) + ConcSplitAEdges(deps, g)
  }

  // ---------------------------------------------------------------------
  // The constructions of Theorems 4.2.4 and 4.2.5.
  // ---------------------------------------------------------------------

  // Theorem 4.2.4: read a concurrent resolution off a core resolution of
  // the reduced instance — keep the granular packages whose granularity
  // tag matches their version.
  function ConcExtractRes(r: set<Package>, g: GranFn): set<Package> {
    set p | p in r && p.name.GranularName? && p.name.gran == g(p.version) ::
      Package(p.name.gbase, p.version)
  }

  // Theorem 4.2.4: the parent relation — for split dependencies the child
  // is reached via the selected intermediate; for direct dependencies it
  // is the selected granular package.
  function ConcRhoSplit(r: set<Package>, deps: DepRel, g: GranFn): ParentRel {
    set e, gam, u | e in deps && IsSplit(e, g)
      && gam in Grans(e.1.versions, g) && u in e.1.versions
      && GPkg(e.0, g) in r
      && Package(IName(e), gam) in r
      && Package(GranularName(e.1.name, gam), u) in r
      :: (Package(e.1.name, u), e.0)
  }

  function ConcRhoDirect(r: set<Package>, deps: DepRel, g: GranFn): ParentRel {
    set e, u | e in deps && !IsSplit(e, g)
      && u in e.1.versions
      && GPkg(e.0, g) in r
      && Package(GranularName(e.1.name, g(u)), u) in r
      :: (Package(e.1.name, u), e.0)
  }

  function ConcExtractRho(r: set<Package>, deps: DepRel, g: GranFn): ParentRel {
    ConcRhoSplit(r, deps, g) + ConcRhoDirect(r, deps, g)
  }

  // Theorem 4.2.5: build a core resolution from a concurrent one — the
  // granular images plus, for each split dependency, the intermediate at
  // the granularity of the ρ-selected child.
  function ConcGranImage(rg: set<Package>, g: GranFn): set<Package> {
    set p | p in rg :: GPkg(p, g)
  }

  function ConcIntChoice(rg: set<Package>, rho: ParentRel, deps: DepRel, g: GranFn): set<Package> {
    set e, u | e in deps && IsSplit(e, g) && e.0 in rg
      && u in e.1.versions && Selected(e, u, rg, rho)
      :: Package(IName(e), g(u))
  }

  function ConcBuildCore(rg: set<Package>, rho: ParentRel, deps: DepRel, g: GranFn): set<Package> {
    ConcGranImage(rg, g) + ConcIntChoice(rg, rho, deps, g)
  }
}
