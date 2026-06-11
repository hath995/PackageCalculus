// Conflicts.dfy — The Conflict Package Calculus (§4.1).
//
// Definitions 4.1.1–4.1.3 of the paper. A conflict (p, (m, S)) means p
// cannot be co-installed with any (m, u) for u ∈ S. The reduction encodes
// each conflict as a synthetic package kappa_{p,(m,S)} with exactly two
// versions, 0 and 1: the declaring package depends on version 1, every
// conflicting package depends on version 0, and version uniqueness makes
// the two sides mutually exclusive.
//
// Theorems 4.1.4 (soundness) and 4.1.5 (completeness) are proved in
// lemmas/ConflictsLemmas.dfy.

include "Core.dfy"

module Conflicts {
  import opened Core

  // Definition 4.1.1: conflicts C ⊆ P × (N × ℘(V)).
  type ConflictRel = set<(Package, Dep)>

  // Definition 4.1.2(b): for every package in the resolution, no package it
  // conflicts with is in the resolution.
  predicate ConflictAvoidance(confl: ConflictRel, r: set<Package>) {
    forall e | e in confl && e.0 in r ::
      forall v | v in e.1.versions :: Package(e.1.name, v) !in r
  }

  // Definition 4.1.2: r ∈ S_C(D, C, root).
  predicate ValidConflictResolution(repo: set<Package>, deps: DepRel, confl: ConflictRel,
                                    root: Package, r: set<Package>) {
    ValidResolution(repo, deps, root, r) && ConflictAvoidance(confl, r)
  }

  // The synthetic conflict package name kappa_{p,(m,S)}. Constructor
  // injectivity gives distinctness of the kappas for distinct conflicts,
  // and freshness with respect to non-ConflictName names, for free.
  function KName(e: (Package, Dep)): Name {
    ConflictName(e.0, e.1.name, e.1.versions)
  }

  // Definition 4.1.3(a): R̂ = R ∪ {kappa@0, kappa@1 | (p,(m,S)) ∈ C}.
  function ReduceRepo(repo: set<Package>, confl: ConflictRel): set<Package> {
    repo + set e, b | e in confl && b in {0 as Version, 1 as Version} :: Package(KName(e), b)
  }

  // Definition 4.1.3(b): the declarer depends on kappa@1; each conflicting
  // package depends on kappa@0.
  function ReduceDeps(deps: DepRel, confl: ConflictRel): DepRel {
    deps
    + (set e | e in confl :: (e.0, Dep(KName(e), {1 as Version})))
    + (set e, v | e in confl && v in e.1.versions ::
        (Package(e.1.name, v), Dep(KName(e), {0 as Version})))
  }

  // Freshness side conditions for the reduction: the original instance
  // mentions no synthetic conflict packages, declarers exist, and conflict
  // targets are ordinary names.
  predicate RealInstance(repo: set<Package>, deps: DepRel, confl: ConflictRel) {
    (forall p | p in repo :: !p.name.ConflictName?)
    && (forall e | e in deps :: !e.1.name.ConflictName?)
    && (forall e | e in confl :: e.0 in repo && !e.1.name.ConflictName?)
  }

  // The completeness witness of Theorem 4.1.5: extend a conflict-calculus
  // resolution with one side of each synthetic conflict package.
  function ExtendWithKappas(r: set<Package>, confl: ConflictRel): set<Package> {
    r
    + (set e | e in confl && e.0 in r :: Package(KName(e), 1 as Version))
    + (set e | e in confl && e.0 !in r :: Package(KName(e), 0 as Version))
  }
}
