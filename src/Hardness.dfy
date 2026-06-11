// Hardness.dfy — The 3-SAT reduction of Theorem 3.1.4 (Appendix B).
//
// NP-hardness of DependencyResolution: for any 3-CNF formula we construct
// a Package Calculus instance such that the formula is satisfiable iff a
// valid resolution exists.
//
//   - one package (x_i, b) per variable i and boolean b (versions 0/1
//     encode false/true);
//   - three packages (c_j, k), k ∈ {1,2,3}, per clause j, one per literal;
//   - a root that depends on each clause name with versions {1,2,3};
//   - (c_j, k) depends on var(l_k) with the single version pol(l_k).
//
// Version uniqueness forces a consistent assignment to each variable, and
// the root's clause dependencies force a satisfied literal per clause.
// The equivalence is proved in lemmas/HardnessLemmas.dfy.

include "Core.dfy"

module Hardness {
  import opened Core

  // A literal: variable index plus polarity; a clause is exactly three
  // literals; a formula is a sequence of clauses.
  datatype Lit = Lit(varIdx: nat, pos: bool)
  datatype Clause3 = Clause3(l1: Lit, l2: Lit, l3: Lit)
  type Formula3 = seq<Clause3>

  predicate WfFormula(f: Formula3, n: nat) {
    forall c | c in f :: c.l1.varIdx < n && c.l2.varIdx < n && c.l3.varIdx < n
  }

  predicate LitHolds(asg: seq<bool>, l: Lit)
    requires l.varIdx < |asg|
  {
    asg[l.varIdx] == l.pos
  }

  // σ satisfies the 3-CNF formula.
  predicate Sat3(asg: seq<bool>, f: Formula3)
    requires WfFormula(f, |asg|)
  {
    forall j | 0 <= j < |f| ::
      LitHolds(asg, f[j].l1) || LitHolds(asg, f[j].l2) || LitHolds(asg, f[j].l3)
  }

  // pol(l): version 1 for positive literals, 0 for negative.
  function B2V(b: bool): Version {
    if b then 1 else 0
  }

  function EncRoot(): Package {
    Package(RootName, 0)
  }

  // The k-th literal of a clause, k ∈ {1,2,3}.
  function ClauseLit(c: Clause3, k: nat): Lit
    requires 1 <= k <= 3
  {
    if k == 1 then c.l1 else if k == 2 then c.l2 else c.l3
  }

  // Appendix B, construction step (1)–(3a): the repository.
  function EncRepo(f: Formula3, n: nat): set<Package> {
    {EncRoot()}
    + (set i, b | 0 <= i < n && b in {false, true} :: Package(VarName(i), B2V(b)))
    + (set j: nat, k: Version | j < |f| && k in {1, 2, 3} :: Package(ClauseName(j), k))
  }

  // Appendix B, construction steps (3b) and (3c): the dependencies.
  function EncDeps(f: Formula3, n: nat): DepRel {
    (set j | 0 <= j < |f| ::
      (EncRoot(), Dep(ClauseName(j), {1 as Version, 2 as Version, 3 as Version})))
    + (set j: nat, k: nat | j < |f| && k in {1, 2, 3} ::
        (Package(ClauseName(j), k as Version),
         Dep(VarName(ClauseLit(f[j], k).varIdx), {B2V(ClauseLit(f[j], k).pos)})))
  }

  // The (⇒) witness of Appendix B: from a satisfying assignment, build the
  // resolution {root} ∪ {(x_i, σ(x_i))} ∪ {(c_j, k_j)} where k_j picks a
  // satisfied literal of clause j.
  function ChooseK(asg: seq<bool>, c: Clause3): nat
    requires c.l1.varIdx < |asg| && c.l2.varIdx < |asg| && c.l3.varIdx < |asg|
    requires LitHolds(asg, c.l1) || LitHolds(asg, c.l2) || LitHolds(asg, c.l3)
    ensures 1 <= ChooseK(asg, c) <= 3
    ensures LitHolds(asg, ClauseLit(c, ChooseK(asg, c)))
  {
    if LitHolds(asg, c.l1) then 1 else if LitHolds(asg, c.l2) then 2 else 3
  }

  function EncWitness(f: Formula3, asg: seq<bool>): set<Package>
    requires WfFormula(f, |asg|)
    requires Sat3(asg, f)
  {
    {EncRoot()}
    + (set i | 0 <= i < |asg| :: Package(VarName(i), B2V(asg[i])))
    + (set j | 0 <= j < |f| :: Package(ClauseName(j), ChooseK(asg, f[j]) as Version))
  }

  // The (⇐) witness: read an assignment off a resolution, σ(x_i) = b where
  // (x_i, b) ∈ r.
  function ExtractAsg(r: set<Package>, n: nat): seq<bool> {
    seq(n, i requires 0 <= i => Package(VarName(i), 1) in r)
  }
}
