// Singular.dfy — Singular dependencies (§4.9).
//
// Definitions 4.9.1 and 4.9.2 of the paper. Nix, Guix, and Unison support
// only a single exact version of a dependee, delegating version selection
// from the resolver to the packager. Singular dependencies restrict the
// core rather than extend it: every singular instance embeds into the core
// by using singleton version sets (proved in lemmas/SingularLemmas.dfy),
// while the converse reduction is impossible since the core can express
// genuine version choice.

include "Core.dfy"

module Singular {
  import opened Core

  // Definition 4.9.1: singular dependencies D_1 ⊆ P × P.
  type SingularRel = set<(Package, Package)>

  // Definition 4.9.2(b): dependency closure — the exact dependee package
  // must be present.
  predicate SingularClosure(sdeps: SingularRel, r: set<Package>) {
    forall e | e in sdeps && e.0 in r :: e.1 in r
  }

  // Definition 4.9.2: r ∈ S_1(D_1, root).
  predicate ValidSingularResolution(repo: set<Package>, sdeps: SingularRel,
                                    root: Package, r: set<Package>) {
    r <= repo
    && RootInclusion(root, r)
    && SingularClosure(sdeps, r)
    && VersionUniqueness(r)
  }

  // The embedding into the core: a singular dependency on package q is a
  // core dependency on name q.name with the singleton version set
  // {q.version}.
  function SingularToCore(sdeps: SingularRel): DepRel {
    set e | e in sdeps :: (e.0, Dep(e.1.name, {e.1.version}))
  }
}
