// ConflictsLemmas.dfy — Proofs for §4.1.
//
//   Theorem 4.1.4 (Soundness):   a valid resolution of the reduced core
//     instance, intersected with the original repository, is a valid
//     resolution of the Conflict Package Calculus. The key step: if both a
//     conflict declarer and a conflicting package were selected, the
//     declarer forces kappa@1 and the conflicting package forces kappa@0,
//     violating version uniqueness.
//   Theorem 4.1.5 (Completeness): a valid conflict-calculus resolution,
//     extended with kappa@1 for each declared conflict whose declarer is
//     selected and kappa@0 otherwise, is valid in the reduced core.

include "../src/Conflicts.dfy"

module ConflictsLemmas {
  import opened Core
  import opened Conflicts

  // Theorem 4.1.4.
  lemma ConflictReductionSound(repo: set<Package>, deps: DepRel, confl: ConflictRel,
                               root: Package, rhat: set<Package>)
    requires WfDeps(repo, deps)
    requires root in repo
    requires ValidResolution(ReduceRepo(repo, confl), ReduceDeps(deps, confl), root, rhat)
    ensures ValidConflictResolution(repo, deps, confl, root, rhat * repo)
  {
    var r := rhat * repo;
    var rdeps := ReduceDeps(deps, confl);

    // Dependency closure for the original dependencies.
    forall e | e in deps && e.0 in r
      ensures exists v :: v in e.1.versions && Package(e.1.name, v) in r
    {
      assert e in rdeps;
      var v :| v in e.1.versions && Package(e.1.name, v) in rhat;
      assert Package(e.1.name, v) in repo;  // WfDeps
    }

    // Conflict avoidance via the kappa packages.
    forall e | e in confl && e.0 in r
      ensures forall v | v in e.1.versions :: Package(e.1.name, v) !in r
    {
      forall v | v in e.1.versions
        ensures Package(e.1.name, v) !in r
      {
        if Package(e.1.name, v) in r {
          // The declarer forces kappa@1 ...
          var declEdge := (e.0, Dep(KName(e), {1 as Version}));
          assert declEdge in rdeps;
          var w1 :| w1 in declEdge.1.versions && Package(declEdge.1.name, w1) in rhat;
          assert Package(KName(e), 1) in rhat;
          // ... and the conflicting package forces kappa@0.
          var tgtEdge := (Package(e.1.name, v), Dep(KName(e), {0 as Version}));
          assert tgtEdge in rdeps;
          var w0 :| w0 in tgtEdge.1.versions && Package(tgtEdge.1.name, w0) in rhat;
          assert Package(KName(e), 0) in rhat;
          // Version uniqueness of rhat is violated.
          assert false;
        }
      }
    }
  }

  // Theorem 4.1.5.
  lemma ConflictReductionComplete(repo: set<Package>, deps: DepRel, confl: ConflictRel,
                                  root: Package, r: set<Package>)
    requires WfDeps(repo, deps)
    requires RealInstance(repo, deps, confl)
    requires ValidConflictResolution(repo, deps, confl, root, r)
    ensures ValidResolution(ReduceRepo(repo, confl), ReduceDeps(deps, confl), root,
                            ExtendWithKappas(r, confl))
  {
    var rhat := ExtendWithKappas(r, confl);
    var rrepo := ReduceRepo(repo, confl);
    var rdeps := ReduceDeps(deps, confl);

    // rhat ⊆ rrepo.
    forall p | p in rhat
      ensures p in rrepo
    {
      if p in r {
        assert p in repo;
      } else {
        var e :| e in confl && (p == Package(KName(e), 1) || p == Package(KName(e), 0));
      }
    }

    // Members of rhat that carry an original (non-kappa) name are in r.
    forall p | p in rhat && !p.name.ConflictName?
      ensures p in r
    {
      if p !in r {
        var e :| e in confl && (p == Package(KName(e), 1) || p == Package(KName(e), 0));
        assert p.name.ConflictName?;
        assert false;
      }
    }

    // Version uniqueness of the extended resolution.
    forall p, q | p in rhat && q in rhat && p.name == q.name
      ensures p.version == q.version
    {
      if p in r && q in r {
        // uniqueness of r
      } else if p.name.ConflictName? {
        // Both are kappa packages of the same conflict: the chosen version
        // is determined by whether the declarer is in r.
        var e1 :| e1 in confl && (p == Package(KName(e1), 1) || p == Package(KName(e1), 0))
               && (e1.0 in r <==> p == Package(KName(e1), 1));
        var e2 :| e2 in confl && (q == Package(KName(e2), 1) || q == Package(KName(e2), 0))
               && (e2.0 in r <==> q == Package(KName(e2), 1));
        assert KName(e1) == KName(e2);
        assert e1.0 == e2.0 && e1.1.name == e2.1.name && e1.1.versions == e2.1.versions;
        assert e1.1 == Dep(e1.1.name, e1.1.versions) && e2.1 == Dep(e2.1.name, e2.1.versions);
        assert e1 == e2;
      } else {
        // Same name, one in r (real name), so neither can be a kappa.
        assert p in r && q in r;
      }
    }

    // Dependency closure over the three groups of reduced edges.
    forall e | e in rdeps && e.0 in rhat
      ensures exists v :: v in e.1.versions && Package(e.1.name, v) in rhat
    {
      if e in deps {
        assert !e.0.name.ConflictName?;  // WfDeps + RealInstance
        assert e.0 in r;
        var v :| v in e.1.versions && Package(e.1.name, v) in r;
        assert Package(e.1.name, v) in rhat;
      } else if exists c :: c in confl && e == (c.0, Dep(KName(c), {1 as Version})) {
        var c :| c in confl && e == (c.0, Dep(KName(c), {1 as Version}));
        assert !c.0.name.ConflictName?;  // RealInstance: c.0 ∈ repo
        assert c.0 in r;
        assert Package(KName(c), 1) in rhat;
        assert 1 in e.1.versions && Package(e.1.name, 1) in rhat;
      } else {
        var c, v :| c in confl && v in c.1.versions
                 && e == (Package(c.1.name, v), Dep(KName(c), {0 as Version}));
        assert !e.0.name.ConflictName?;  // RealInstance: conflict targets are real names
        assert e.0 in r;
        // Conflict avoidance: the target is selected, so the declarer is not.
        assert c.0 !in r;
        assert Package(KName(c), 0) in rhat;
        assert 0 in e.1.versions && Package(e.1.name, 0) in rhat;
      }
    }
  }
}
