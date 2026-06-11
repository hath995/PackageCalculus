// SatEncodingLemmas.dfy — Proofs for Appendix C.
//
//   Theorem C.2 (Soundness):   any assignment satisfying Φ induces a valid
//                              resolution (its true-set restricted to repo).
//   Theorem C.3 (Completeness): any valid resolution, read as an
//                              assignment, satisfies Φ.

include "../src/SatEncoding.dfy"

module SatEncodingLemmas {
  import opened Core
  import opened SatEncoding

  // Theorem C.2.
  lemma EncodeSound(repo: set<Package>, deps: DepRel, root: Package, tru: set<Package>)
    requires WfDeps(repo, deps)
    requires root in repo
    requires SatCnf(tru, Encode(repo, deps, root))
    ensures ValidResolution(repo, deps, root, tru * repo)
  {
    var r := tru * repo;
    var cnf := Encode(repo, deps, root);

    // Root inclusion: the unit clause {x_root}.
    assert {PPos(root)} in cnf;
    var l :| l in {PPos(root)} && LitHolds(tru, l);
    assert root in tru;

    // Dependency closure.
    forall e | e in deps && e.0 in r
      ensures exists v :: v in e.1.versions && Package(e.1.name, v) in r
    {
      var c := {PNeg(e.0)} + set v | v in e.1.versions :: PPos(Package(e.1.name, v));
      assert c in ClosureClauses(deps);
      assert ClauseHolds(tru, c);
      var l :| l in c && LitHolds(tru, l);
      if l == PNeg(e.0) {
        assert e.0 !in tru;  // contradicts e.0 ∈ r ⊆ tru
        assert false;
      } else {
        var v :| v in e.1.versions && l == PPos(Package(e.1.name, v));
        assert Package(e.1.name, v) in tru;
        assert Package(e.1.name, v) in repo;  // WfDeps
      }
    }

    // Version uniqueness: the pairwise clauses forbid co-selection.
    forall p, q | p in r && q in r && p.name == q.name
      ensures p.version == q.version
    {
      if p != q {
        var c := {PNeg(p), PNeg(q)};
        assert c in UniquenessClauses(repo);
        assert ClauseHolds(tru, c);
        var l :| l in c && LitHolds(tru, l);
        assert p !in tru || q !in tru;
        assert false;
      }
    }
  }

  // Theorem C.3.
  lemma EncodeComplete(repo: set<Package>, deps: DepRel, root: Package, r: set<Package>)
    requires ValidResolution(repo, deps, root, r)
    ensures SatCnf(r, Encode(repo, deps, root))
  {
    var cnf := Encode(repo, deps, root);
    forall c | c in cnf
      ensures ClauseHolds(r, c)
    {
      if c == {PPos(root)} {
        assert PPos(root) in c && LitHolds(r, PPos(root));
      } else if c in ClosureClauses(deps) {
        var e :| e in deps
          && c == {PNeg(e.0)} + set v | v in e.1.versions :: PPos(Package(e.1.name, v));
        if e.0 in r {
          var v :| v in e.1.versions && Package(e.1.name, v) in r;
          var l := PPos(Package(e.1.name, v));
          assert l in c && LitHolds(r, l);
        } else {
          assert PNeg(e.0) in c && LitHolds(r, PNeg(e.0));
        }
      } else {
        assert c in UniquenessClauses(repo);
        var p, q :| p in repo && q in repo && p.name == q.name && p != q
                 && c == {PNeg(p), PNeg(q)};
        if p in r && q in r {
          assert p.version == q.version;  // VersionUniqueness
          assert p == q;
          assert false;
        }
        if p !in r {
          assert PNeg(p) in c && LitHolds(r, PNeg(p));
        } else {
          assert PNeg(q) in c && LitHolds(r, PNeg(q));
        }
      }
    }
  }
}
