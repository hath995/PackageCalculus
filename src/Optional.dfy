// Optional.dfy — Build graphs and optional dependencies (§4.8).
//
// Definitions 4.8.1 and 4.8.2 of the paper. Optional dependencies are
// purely a build-graph consideration: they order installation when the
// optional dependee happens to be in the resolution, but the resolver
// neither includes nor excludes packages because of them. The paper's
// claim — the reduction to the core simply omits O, so S(D, root) is
// unchanged — is stated and proved in lemmas/OptionalLemmas.dfy, and
// Example 4.8.3 is executed in tests/Examples.dfy.

include "Core.dfy"

module Optional {
  import opened Core

  // Definition 4.8.2: optional dependencies O ⊆ P × (N × ℘(V)), the same
  // shape as ordinary dependencies.
  type OptRel = set<(Package, Dep)>

  // Definition 4.8.1: the build graph of a resolution — an edge from each
  // depender in r to the selected dependee in r.
  function BuildGraph(deps: DepRel, r: set<Package>): set<(Package, Package)> {
    set e, v | e in deps && e.0 in r && v in e.1.versions && Package(e.1.name, v) in r ::
      (e.0, Package(e.1.name, v))
  }

  // Definition 4.8.2 (second part): optional dependees, when present in the
  // resolution, are required before their depender — the same edge shape.
  function BuildGraphOpt(deps: DepRel, opt: OptRel, r: set<Package>): set<(Package, Package)> {
    BuildGraph(deps, r) + BuildGraph(opt, r)
  }

  // §4.8: a resolution of the Optional Dependency calculus is valid exactly
  // when it is valid in the core; O plays no part. (Stating it this way
  // makes the paper's "trivial reduction by omission" a checkable claim —
  // see lemmas/OptionalLemmas.dfy.)
  predicate ValidOptResolution(repo: set<Package>, deps: DepRel, opt: OptRel,
                               root: Package, r: set<Package>) {
    ValidResolution(repo, deps, root, r)
  }
}
