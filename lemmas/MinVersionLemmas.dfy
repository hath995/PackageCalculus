// MinVersionLemmas.dfy — Proofs for §3.3.
//
// Approach (1), minimum bounds:
//   MvsValid          — the canonical greedy (least visited set, per-name
//                       maxima) yields a valid resolution: greedy suffices,
//                       no backtracking, every well-formed instance with a
//                       fresh root name is solvable.
//   MvsDeterministic  — the least visited set is unique, so the resolution
//                       is determined by the minimum bounds alone ("lock
//                       files are unnecessary under MVS").
//   UpgradeToleratesBounds — without upper bounds, pointwise upgrades never
//                       violate dependers' constraints.
//   MinVfEquiv / MinToCoreCorrect — the min-bound calculus is the
//                       ≥-fragment of the Version Formula Calculus, and so
//                       reduces to the core via Theorem 3.2.7.
//
// Approach (2), no version uniqueness:
//   CoreImpliesMulti, MultiToConcurrentIdentity, ConcurrentToMulti —
//   uniqueness-free resolution is the Concurrent Package Calculus with the
//   identity granularity function (§2.2.7's "for npm or Nix g(v) = v").
//
// See FINDINGS.md §3.3 for the two qualifications these proofs surfaced
// (the fresh-root hypothesis, and determinism versus minimality).

include "../src/MinVersion.dfy"
include "../src/Concurrent.dfy"
include "VersionsLemmas.dfy"

module MinVersionLemmas {
  import opened Core
  import opened Versions
  import opened MinVersion
  import opened Concurrent
  import VersionsLemmas

  // ---------------------------------------------------------------------
  // Approach (1).
  // ---------------------------------------------------------------------

  // Least closed sets are unique: the MVS answer is a function of the
  // instance.
  lemma MvsDeterministic(mdeps: MinDepRel, root: Package,
                         v1: set<Package>, v2: set<Package>)
    requires IsMinVisited(mdeps, root, v1)
    requires IsMinVisited(mdeps, root, v2)
    ensures v1 == v2 && MvsOf(v1) == MvsOf(v2)
  {
  }

  // With a fresh root name, the root is the only visited version of its
  // name.
  lemma RootOnlyVersion(mdeps: MinDepRel, root: Package, visited: set<Package>)
    requires IsMinVisited(mdeps, root, visited)
    requires FreshRootName(mdeps, root)
    ensures forall q | q in visited && q.name == root.name :: q == root
  {
    var w := set q | q in visited && (q.name != root.name || q == root) :: q;
    assert root in w;
    forall e | e in mdeps && e.0 in w
      ensures Package(e.1.name, e.1.bound) in w
    {
      assert Package(e.1.name, e.1.bound) in visited;
      assert e.1.name != root.name;
    }
    assert MinClosedSet(mdeps, w);
    assert visited <= w;
  }

  // Theorem (§3.3, approach 1): the canonical greedy output is a valid
  // resolution. Together with MvsVisited's postcondition this shows every
  // well-formed instance with a fresh root name is solvable without
  // backtracking.
  lemma MvsValid(repo: set<Package>, mdeps: MinDepRel, root: Package, visited: set<Package>)
    requires WfMinDeps(repo, mdeps)
    requires root in repo
    requires FreshRootName(mdeps, root)
    requires IsMinVisited(mdeps, root, visited)
    requires visited <= repo
    ensures ValidMinResolution(repo, mdeps, root, MvsOf(visited))
  {
    var r := MvsOf(visited);

    // r ⊆ repo: each maximum is itself a visited package.
    forall p | p in r
      ensures p in visited
    {
      var q :| q in visited && p == NameMaxIn(visited, q);
      var vmax := SetMax(VersionsOfName(visited, q.name));
      var q1 :| q1 in visited && q1.name == q.name && q1.version == vmax;
      assert p == q1;
    }

    // Version uniqueness: one maximum per name.
    forall p, q | p in r && q in r && p.name == q.name
      ensures p.version == q.version
    {
      var p0 :| p0 in visited && p == NameMaxIn(visited, p0);
      var q0 :| q0 in visited && q == NameMaxIn(visited, q0);
      assert p0.name == q0.name;
    }

    // Root inclusion: the root is its name's only visited version.
    RootOnlyVersion(mdeps, root, visited);
    assert VersionsOfName(visited, root.name) == {root.version};
    assert NameMaxIn(visited, root) == root;
    assert root in r;

    // Minimum-bound closure: the visited set is bound-closed, and maxima
    // dominate every bound.
    forall e | e in mdeps && e.0 in r
      ensures exists q | q in r :: q.name == e.1.name && e.1.bound <= q.version
    {
      assert e.0 in visited;  // shown above: r ⊆ visited
      assert Package(e.1.name, e.1.bound) in visited;  // MinClosedSet
      var cand := NameMaxIn(visited, Package(e.1.name, e.1.bound));
      assert cand in r;
      assert e.1.bound in VersionsOfName(visited, e.1.name);
      assert cand.name == e.1.name && e.1.bound <= cand.version;
    }
  }

  // §3.3: "without upper bounds, any version above the maximum of all
  // minimum bounds is valid" — dependers' bound constraints are monotone
  // under pointwise upgrades. (Outgoing dependencies of the new versions
  // must still be re-closed; in the core calculus, with upper bounds, even
  // this monotonicity fails.)
  predicate PointwiseGeq(r: set<Package>, r': set<Package>) {
    forall q | q in r ::
      exists q' | q' in r' :: q'.name == q.name && q.version <= q'.version
  }

  lemma UpgradeToleratesBounds(mdeps: MinDepRel, r: set<Package>, r': set<Package>)
    requires MinClosure(mdeps, r)
    requires PointwiseGeq(r, r')
    ensures forall e | e in mdeps && e.0 in r ::
      exists q' | q' in r' :: q'.name == e.1.name && e.1.bound <= q'.version
  {
    forall e | e in mdeps && e.0 in r
      ensures exists q' | q' in r' :: q'.name == e.1.name && e.1.bound <= q'.version
    {
      var q :| q in r && q.name == e.1.name && e.1.bound <= q.version;
      var q' :| q' in r' && q'.name == q.name && q.version <= q'.version;
    }
  }

  // The min-bound calculus is the ≥-fragment of the Version Formula
  // Calculus (§3.2).
  lemma MinVfEquiv(repo: set<Package>, mdeps: MinDepRel, root: Package, r: set<Package>)
    ensures ValidMinResolution(repo, mdeps, root, r)
        <==> ValidVfResolution(repo, MinToVf(mdeps), root, r)
  {
    var vdeps := MinToVf(mdeps);
    if r <= repo {
      forall e | e in mdeps
        ensures (exists q | q in r :: q.name == e.1.name && e.1.bound <= q.version)
            <==> (exists u :: u in Eval(VCmp(Ge, e.1.bound), VersionsOf(repo, e.1.name))
                           && Package(e.1.name, u) in r)
      {
        if q :| q in r && q.name == e.1.name && e.1.bound <= q.version {
          assert q in repo;
          assert q.version in VersionsOf(repo, e.1.name);
          assert q.version in Eval(VCmp(Ge, e.1.bound), VersionsOf(repo, e.1.name));
          assert Package(e.1.name, q.version) == q;
        }
        if u :| u in Eval(VCmp(Ge, e.1.bound), VersionsOf(repo, e.1.name))
             && Package(e.1.name, u) in r {
          assert Package(e.1.name, u).name == e.1.name && e.1.bound <= u;
        }
      }
      if MinClosure(mdeps, r) {
        forall e' | e' in vdeps && e'.0 in r
          ensures exists u :: u in Eval(e'.1.formula, VersionsOf(repo, e'.1.name))
                           && Package(e'.1.name, u) in r
        {
          var e :| e in mdeps && e' == (e.0, VfDep(e.1.name, VCmp(Ge, e.1.bound)));
        }
      }
      if VfDepClosure(repo, vdeps, r) {
        forall e | e in mdeps && e.0 in r
          ensures exists q | q in r :: q.name == e.1.name && e.1.bound <= q.version
        {
          var e' := (e.0, VfDep(e.1.name, VCmp(Ge, e.1.bound)));
          assert e' in vdeps;
        }
      }
    }
  }

  // ... and hence reduces to the core calculus, by Theorem 3.2.7.
  lemma MinToCoreCorrect(repo: set<Package>, mdeps: MinDepRel, root: Package, r: set<Package>)
    ensures ValidMinResolution(repo, mdeps, root, r)
        <==> ValidResolution(repo, ReduceVf(repo, MinToVf(mdeps)), root, r)
  {
    MinVfEquiv(repo, mdeps, root, r);
    VersionsLemmas.VfReductionCorrect(repo, MinToVf(mdeps), root, r);
  }

  // ---------------------------------------------------------------------
  // Approach (2).
  // ---------------------------------------------------------------------

  // Dropping a condition only grows the solution set.
  lemma CoreImpliesMulti(repo: set<Package>, deps: DepRel, root: Package, r: set<Package>)
    requires ValidResolution(repo, deps, root, r)
    ensures MultiValid(repo, deps, root, r)
  {
  }

  // A ρ pair of the canonical maximal selection pins the version.
  lemma MaxRhoPins(deps: DepRel, r: set<Package>, e: (Package, Dep), v: Version)
    requires UniqueDepPerName(deps)
    requires e in deps
    requires (Package(e.1.name, v), e.0) in MaxSelRho(deps, r)
    ensures SelVers(e, r) != {} && v == SetMax(SelVers(e, r))
  {
    var e' :| e' in deps && e'.0 in r && SelVers(e', r) != {}
          && (Package(e'.1.name, SetMax(SelVers(e', r))), e'.0)
             == (Package(e.1.name, v), e.0);
    assert e' == e;  // UniqueDepPerName
  }

  // §3.3(2) is the Concurrent Package Calculus at identity granularity:
  // a uniqueness-free resolution, with each dependency witnessed by its
  // maximal selected version, is a valid concurrent resolution ...
  lemma MultiToConcurrentIdentity(repo: set<Package>, deps: DepRel, g: GranFn,
                                  root: Package, r: set<Package>)
    requires forall v: Version :: g(v) == v
    requires UniqueDepPerName(deps)
    requires MultiValid(repo, deps, root, r)
    ensures ValidConcurrentResolution(repo, deps, g, root, r, MaxSelRho(deps, r))
  {
    var rho := MaxSelRho(deps, r);
    forall e | e in deps && e.0 in r
      ensures (exists v | v in e.1.versions :: Selected(e, v, r, rho))
           && (forall v1, v2 | v1 in e.1.versions && v2 in e.1.versions
                 && Selected(e, v1, r, rho) && Selected(e, v2, r, rho) :: v1 == v2)
    {
      var u :| u in e.1.versions && Package(e.1.name, u) in r;
      assert u in SelVers(e, r);
      var m := SetMax(SelVers(e, r));
      assert (Package(e.1.name, m), e.0) in rho;
      assert m in SelVers(e, r);
      assert Selected(e, m, r, rho);
      forall v1, v2 | v1 in e.1.versions && v2 in e.1.versions
            && Selected(e, v1, r, rho) && Selected(e, v2, r, rho)
        ensures v1 == v2
      {
        MaxRhoPins(deps, r, e, v1);
        MaxRhoPins(deps, r, e, v2);
      }
    }
  }

  // ... and conversely, any concurrent resolution (any granularity) is a
  // valid uniqueness-free resolution.
  lemma ConcurrentToMulti(repo: set<Package>, deps: DepRel, g: GranFn,
                          root: Package, r: set<Package>, rho: ParentRel)
    requires ValidConcurrentResolution(repo, deps, g, root, r, rho)
    ensures MultiValid(repo, deps, root, r)
  {
    forall e | e in deps && e.0 in r
      ensures exists v :: v in e.1.versions && Package(e.1.name, v) in r
    {
      var v :| v in e.1.versions && Selected(e, v, r, rho);
    }
  }
}
