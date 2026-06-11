// SatEncoding.dfy — SAT-based dependency resolution (Appendix C).
//
// Definition C.1 of the paper: the reduction of DependencyResolution to
// SAT. One boolean variable x_p per package p in the repository; clauses
// for root inclusion, dependency closure (¬x_p ∨ ⋁_{u ∈ S} x_{(m,u)}), and
// pairwise version uniqueness (¬x_{(n,v)} ∨ ¬x_{(n,v')}).
//
// Theorems C.2 (soundness) and C.3 (completeness) are proved in
// lemmas/SatEncodingLemmas.dfy.

include "Core.dfy"

module SatEncoding {
  import opened Core

  // Literals over package variables x_p; an assignment is represented by
  // its true-set tru ⊆ P (x_p is true iff p ∈ tru).
  datatype PLit = PPos(p: Package) | PNeg(p: Package)
  type PClause = set<PLit>
  type PCnf = set<PClause>

  predicate LitHolds(tru: set<Package>, l: PLit) {
    match l
    case PPos(p) => p in tru
    case PNeg(p) => p !in tru
  }

  predicate ClauseHolds(tru: set<Package>, c: PClause) {
    exists l :: l in c && LitHolds(tru, l)
  }

  predicate SatCnf(tru: set<Package>, cnf: PCnf) {
    forall c | c in cnf :: ClauseHolds(tru, c)
  }

  // Definition C.1(b)(i): dependency closure clauses.
  function ClosureClauses(deps: DepRel): PCnf {
    set e | e in deps ::
      {PNeg(e.0)} + set v | v in e.1.versions :: PPos(Package(e.1.name, v))
  }

  // Definition C.1(b)(ii): pairwise version-uniqueness clauses; O(k²) per
  // name with k versions, as the paper notes.
  function UniquenessClauses(repo: set<Package>): PCnf {
    set p, q | p in repo && q in repo && p.name == q.name && p != q ::
      {PNeg(p), PNeg(q)}
  }

  // Definition C.1: Φ := x_root ∧ closure ∧ uniqueness.
  function Encode(repo: set<Package>, deps: DepRel, root: Package): PCnf {
    {{PPos(root)}} + ClosureClauses(deps) + UniquenessClauses(repo)
  }
}
