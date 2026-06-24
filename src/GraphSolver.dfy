// GraphSolver.dfy — a runnable resolver for the provenance graph.
//
// Reuses the verified core resolver (Solver.AllResolutions) over the reduction
// of src/ProvenanceGraph.dfy: a Universe becomes a repository plus a version-
// formula dependency relation (ToVfDeps), which ReduceVf turns into an ordinary
// core DepRel. ResolveGraph runs the resolver on that and returns every valid
// resolution. Its postcondition is given both in core terms (a complete
// characterisation) and in graph terms (each selection's package set is
// returned iff it is a valid graph resolution rooted at the requested version).

include "ProvenanceGraph.dfy"
include "Solver.dfy"
include "../lemmas/ProvenanceGraphLemmas.dfy"

module GraphSolver {
  import opened Core
  import opened Versions
  import opened Provenance
  import opened ProvenanceGraph
  import opened ProvenanceGraphLemmas
  import opened Solver

  // Compute every valid resolution of the graph rooted at Package(rootName,
  // rootVersion). Runnable: it enumerates and checks, reusing AllResolutions.
  method ResolveGraph(u: Universe, rootName: Name, rootVersion: Version)
    returns (rs: set<set<Package>>)
    requires WfGraph(u)
    // Complete characterisation: exactly the core resolutions of the reduction.
    ensures forall r :: r in rs <==>
              ValidResolution(Repo(u), ReduceVf(Repo(u), ToVfDeps(u)),
                              Package(rootName, rootVersion), r)
    // Graph meaning: a selection's package set is returned iff it is a valid
    // graph resolution that pins the root to the requested version.
    ensures forall sel: map<Name, Version> | rootName in sel ::
              SelToSet(sel) in rs <==>
                (sel[rootName] == rootVersion && ValidGraphResolution(u, rootName, sel))
  {
    var repo := Repo(u);
    var deps := ReduceVf(repo, ToVfDeps(u));
    rs := AllResolutions(repo, deps, Package(rootName, rootVersion));

    forall sel: map<Name, Version> | rootName in sel
      ensures SelToSet(sel) in rs <==>
                (sel[rootName] == rootVersion && ValidGraphResolution(u, rootName, sel))
    {
      GraphReducesToCore(u, rootName, sel);
      // RootInclusion of the requested root forces sel[rootName] == rootVersion.
      SelMem(sel, Package(rootName, rootVersion));
    }
  }
}
