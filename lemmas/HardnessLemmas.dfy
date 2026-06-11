// HardnessLemmas.dfy — Proofs for Appendix B (Theorem 3.1.4, NP-hardness).
//
//   SatGivesResolution  (⇒): a satisfying assignment yields a valid
//                            resolution of the encoded instance.
//   ResolutionGivesSat  (⇐): a valid resolution of the encoded instance
//                            induces a satisfying assignment.
//   HardnessCorrect:         the equivalence — the 3-CNF formula is
//                            satisfiable iff S(D, root) is non-empty.
//
// Together with the executable validity checker (NP membership; the
// ValidResolution predicate is compiled and runs in polynomial time),
// this mechanises both halves of Theorem 3.1.4's proof.

include "../src/Hardness.dfy"

module HardnessLemmas {
  import opened Core
  import opened Hardness

  // Appendix B, direction (⇒).
  lemma SatGivesResolution(f: Formula3, asg: seq<bool>)
    requires WfFormula(f, |asg|)
    requires Sat3(asg, f)
    ensures ValidResolution(EncRepo(f, |asg|), EncDeps(f, |asg|), EncRoot(), EncWitness(f, asg))
  {
    var n := |asg|;
    var repo := EncRepo(f, n);
    var deps := EncDeps(f, n);
    var w := EncWitness(f, asg);
    var varPart := set i | 0 <= i < n :: Package(VarName(i), B2V(asg[i]));
    var clausePart := set j | 0 <= j < |f| :: Package(ClauseName(j), ChooseK(asg, f[j]) as Version);
    assert w == {EncRoot()} + varPart + clausePart;

    // w ⊆ repo.
    forall p | p in w
      ensures p in repo
    {
      if p in varPart {
        var i :| 0 <= i < n && p == Package(VarName(i), B2V(asg[i]));
        assert asg[i] in {false, true};
      } else if p in clausePart {
        var j :| 0 <= j < |f| && p == Package(ClauseName(j), ChooseK(asg, f[j]) as Version);
        var k: Version := ChooseK(asg, f[j]) as Version;
        assert k in {1 as Version, 2 as Version, 3 as Version};
      }
    }

    // Version uniqueness: each name appears with exactly one version.
    forall p, q | p in w && q in w && p.name == q.name
      ensures p.version == q.version
    {
      if p in varPart {
        var i1 :| 0 <= i1 < n && p == Package(VarName(i1), B2V(asg[i1]));
        assert q != EncRoot() && q !in clausePart;
        var i2 :| 0 <= i2 < n && q == Package(VarName(i2), B2V(asg[i2]));
        assert i1 == i2;
      } else if p in clausePart {
        var j1 :| 0 <= j1 < |f| && p == Package(ClauseName(j1), ChooseK(asg, f[j1]) as Version);
        assert q != EncRoot() && q !in varPart;
        var j2 :| 0 <= j2 < |f| && q == Package(ClauseName(j2), ChooseK(asg, f[j2]) as Version);
        assert j1 == j2;
      } else {
        assert p == EncRoot();
        assert q == EncRoot();
      }
    }

    // Dependency closure.
    forall e | e in deps && e.0 in w
      ensures exists v :: v in e.1.versions && Package(e.1.name, v) in w
    {
      if e.0 == EncRoot() && e.1.name.ClauseName? {
        // Root → clause j: the chosen literal's index witnesses the clause.
        var j :| 0 <= j < |f|
              && e == (EncRoot(), Dep(ClauseName(j), {1 as Version, 2 as Version, 3 as Version}));
        var k: Version := ChooseK(asg, f[j]) as Version;
        assert Package(ClauseName(j), k) in clausePart;
        assert k in e.1.versions && Package(e.1.name, k) in w;
      } else {
        // Clause package (c_j, k) → its literal's variable package.
        var j: nat, k: nat :| j < |f| && k in {1, 2, 3}
          && e == (Package(ClauseName(j), k as Version),
                   Dep(VarName(ClauseLit(f[j], k).varIdx), {B2V(ClauseLit(f[j], k).pos)}));
        // e.0 ∈ w and e.0 is a clause package, so k is the chosen literal.
        assert e.0 != EncRoot() && e.0 !in varPart;
        var j2 :| 0 <= j2 < |f| && e.0 == Package(ClauseName(j2), ChooseK(asg, f[j2]) as Version);
        assert j2 == j && k == ChooseK(asg, f[j]);
        var lit := ClauseLit(f[j], k);
        assert LitHolds(asg, lit);             // ChooseK's postcondition
        assert lit.varIdx < n;                 // WfFormula
        assert Package(VarName(lit.varIdx), B2V(asg[lit.varIdx])) in varPart;
        assert B2V(asg[lit.varIdx]) == B2V(lit.pos);
        assert B2V(lit.pos) in e.1.versions && Package(e.1.name, B2V(lit.pos)) in w;
      }
    }
  }

  // Appendix B, direction (⇐).
  lemma ResolutionGivesSat(f: Formula3, n: nat, r: set<Package>)
    requires WfFormula(f, n)
    requires ValidResolution(EncRepo(f, n), EncDeps(f, n), EncRoot(), r)
    ensures Sat3(ExtractAsg(r, n), f)
  {
    var asg := ExtractAsg(r, n);
    assert |asg| == n;
    var deps := EncDeps(f, n);

    forall j | 0 <= j < |f|
      ensures LitHolds(asg, f[j].l1) || LitHolds(asg, f[j].l2) || LitHolds(asg, f[j].l3)
    {
      // The root's dependency on clause j selects some (c_j, k).
      var rootEdge := (EncRoot(), Dep(ClauseName(j), {1 as Version, 2 as Version, 3 as Version}));
      assert rootEdge in deps;
      var kv :| kv in rootEdge.1.versions && Package(ClauseName(j), kv) in r;
      var k: nat := kv as nat;
      assert k in {1, 2, 3};
      var lit := ClauseLit(f[j], k);

      // (c_j, k)'s dependency selects the literal's variable package.
      var litEdge := (Package(ClauseName(j), k as Version),
                      Dep(VarName(lit.varIdx), {B2V(lit.pos)}));
      assert litEdge in deps;
      var bv :| bv in litEdge.1.versions && Package(VarName(lit.varIdx), bv) in r;
      assert bv == B2V(lit.pos);

      // The assignment read off r agrees with the literal's polarity.
      var i := lit.varIdx;
      assert i < n;  // WfFormula
      if lit.pos {
        assert Package(VarName(i), 1) in r;
        assert asg[i] == true;
      } else {
        assert Package(VarName(i), 0) in r;
        // Version uniqueness: (x_i, 1) cannot also be selected.
        assert Package(VarName(i), 1) !in r;
        assert asg[i] == false;
      }
      assert LitHolds(asg, lit);
      if k == 1 {
        assert lit == f[j].l1;
      } else if k == 2 {
        assert lit == f[j].l2;
      } else {
        assert lit == f[j].l3;
      }
    }
  }

  // Theorem 3.1.4, NP-hardness: satisfiability ⟺ resolution existence.
  lemma HardnessCorrect(f: Formula3, n: nat)
    requires WfFormula(f, n)
    ensures (exists asg: seq<bool> :: |asg| == n && Sat3(asg, f))
        <==> (exists r :: ValidResolution(EncRepo(f, n), EncDeps(f, n), EncRoot(), r))
  {
    if asg: seq<bool> :| |asg| == n && Sat3(asg, f) {
      SatGivesResolution(f, asg);
      assert ValidResolution(EncRepo(f, n), EncDeps(f, n), EncRoot(), EncWitness(f, asg));
    }
    if r :| ValidResolution(EncRepo(f, n), EncDeps(f, n), EncRoot(), r) {
      ResolutionGivesSat(f, n, r);
      var asg := ExtractAsg(r, n);
      assert |asg| == n && Sat3(asg, f);
    }
  }
}
