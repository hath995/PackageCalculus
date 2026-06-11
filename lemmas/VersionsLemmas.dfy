// VersionsLemmas.dfy — Proofs for §3.2.
//
//   - Definition 3.2.2 claims the resolution ordering is a partial order
//     on S(D, root): we prove reflexivity, transitivity, and antisymmetry
//     (antisymmetry needs version uniqueness, which members of S(D, root)
//     have by Definition 3.1.3(c)).
//   - Theorem 3.2.7: correctness of the version formula reduction,
//     r ∈ S(D, root) ⟺ r ∈ S_φ(D_φ, root).

include "../src/Versions.dfy"

module VersionsLemmas {
  import opened Core
  import opened Versions

  lemma ResLeqRefl(r: set<Package>)
    ensures ResLeq(r, r)
  {
    forall p2 | p2 in r
      ensures exists p1 :: p1 in r && p1.name == p2.name && p1.version <= p2.version
    {
      assert p2 in r && p2.name == p2.name && p2.version <= p2.version;
    }
  }

  lemma ResLeqTrans(r1: set<Package>, r2: set<Package>, r3: set<Package>)
    requires ResLeq(r1, r2) && ResLeq(r2, r3)
    ensures ResLeq(r1, r3)
  {
    forall p3 | p3 in r3
      ensures exists p1 :: p1 in r1 && p1.name == p3.name && p1.version <= p3.version
    {
      var p2 :| p2 in r2 && p2.name == p3.name && p2.version <= p3.version;
      var p1 :| p1 in r1 && p1.name == p2.name && p1.version <= p2.version;
      assert p1 in r1 && p1.name == p3.name && p1.version <= p3.version;
    }
  }

  // Antisymmetry holds on resolutions (Definition 3.1.3(c) gives version
  // uniqueness); on arbitrary package sets the ordering is only a preorder.
  lemma ResLeqAntisym(r1: set<Package>, r2: set<Package>)
    requires VersionUniqueness(r1) && VersionUniqueness(r2)
    requires ResLeq(r1, r2) && ResLeq(r2, r1)
    ensures r1 == r2
  {
    forall p2 | p2 in r2
      ensures p2 in r1
    {
      var p1 :| p1 in r1 && p1.name == p2.name && p1.version <= p2.version;
      var p2' :| p2' in r2 && p2'.name == p1.name && p2'.version <= p1.version;
      assert p2'.version == p2.version;  // uniqueness in r2
      assert p1.version == p2.version;
      assert p1 == p2;
    }
    forall p1 | p1 in r1
      ensures p1 in r2
    {
      var p2 :| p2 in r2 && p2.name == p1.name && p2.version <= p1.version;
      var p1' :| p1' in r1 && p1'.name == p2.name && p1'.version <= p2.version;
      assert p1'.version == p1.version;  // uniqueness in r1
      assert p2 == p1;
    }
  }

  // Theorem 3.2.7 (Correctness): r ∈ S(D, root) ⟺ r ∈ S_φ(D_φ, root),
  // where D := ReduceVf(repo, D_φ) evaluates each formula to its version
  // set (Definition 3.2.6).
  lemma VfReductionCorrect(repo: set<Package>, vdeps: VfDepRel, root: Package, r: set<Package>)
    ensures ValidResolution(repo, ReduceVf(repo, vdeps), root, r)
        <==> ValidVfResolution(repo, vdeps, root, r)
  {
    var deps := ReduceVf(repo, vdeps);

    // Dependency closure of the reduction implies formula closure ...
    if DepClosure(deps, r) {
      forall e | e in vdeps && e.0 in r
        ensures exists u :: u in Eval(e.1.formula, VersionsOf(repo, e.1.name))
                         && Package(e.1.name, u) in r
      {
        var red := (e.0, Dep(e.1.name, Eval(e.1.formula, VersionsOf(repo, e.1.name))));
        assert red in deps;
      }
      assert VfDepClosure(repo, vdeps, r);
    }

    // ... and conversely.
    if VfDepClosure(repo, vdeps, r) {
      forall e | e in deps && e.0 in r
        ensures exists v :: v in e.1.versions && Package(e.1.name, v) in r
      {
        var src :| src in vdeps
          && e == (src.0, Dep(src.1.name, Eval(src.1.formula, VersionsOf(repo, src.1.name))));
        var u :| u in Eval(src.1.formula, VersionsOf(repo, src.1.name))
              && Package(src.1.name, u) in r;
        assert u in e.1.versions && Package(e.1.name, u) in r;
      }
      assert DepClosure(deps, r);
    }
  }
}
