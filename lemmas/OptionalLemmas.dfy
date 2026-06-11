// OptionalLemmas.dfy — Proofs for §4.8.
//
// The paper's claim: optional dependencies reduce trivially to the core by
// omission — they have no effect on the resolution, only on the build
// graph. With ValidOptResolution defined per §4.8 (the resolver ignores
// O), this is the statement that validity is independent of O, and that
// the optional build graph only ever adds ordering edges.

include "../src/Optional.dfy"

module OptionalLemmas {
  import opened Core
  import opened Optional

  // S_O(D, O, root) = S(D, root): the resolution is unaffected by O.
  lemma OptionalIrrelevantToResolution(repo: set<Package>, deps: DepRel,
                                       opt1: OptRel, opt2: OptRel,
                                       root: Package, r: set<Package>)
    ensures ValidOptResolution(repo, deps, opt1, root, r)
        <==> ValidOptResolution(repo, deps, opt2, root, r)
  {
  }

  // Optional dependencies only add edges to the build graph.
  lemma BuildGraphMonotone(deps: DepRel, opt: OptRel, r: set<Package>)
    ensures BuildGraph(deps, r) <= BuildGraphOpt(deps, opt, r)
  {
  }

  // §4.8: "if p →O (m, S) and (m, u) ∈ r with u ∈ S, then the edge is in
  // the build graph always, and there is no mechanism to disable it."
  lemma OptionalEdgeAlwaysPresent(deps: DepRel, opt: OptRel, r: set<Package>,
                                  e: (Package, Dep), u: Version)
    requires e in opt && e.0 in r
    requires u in e.1.versions && Package(e.1.name, u) in r
    ensures (e.0, Package(e.1.name, u)) in BuildGraphOpt(deps, opt, r)
  {
  }
}
