// MinVersion.dfy — The two tractable restrictions of §3.3.
//
// Approach (1): version constraints restricted to minimum bounds (Go's
// minimum version selection). A dependency min(m, l) is satisfied by any
// selected version of m at or above l; the dependency closure condition of
// Definition 3.1.3(b) is replaced accordingly, and version uniqueness is
// kept. Resolution reduces to a reachability closure plus per-name maxima
// — Cox's MVS algorithm — implemented and verified here.
//
// Approach (2): version uniqueness removed (npm/Nix-style duplication).
// Resolution reduces to plain graph reachability, taking every compatible
// version; implemented and verified here, and related to the Concurrent
// Package Calculus with identity granularity in the lemmas.
//
// Mechanisation notes (see FINDINGS.md §3.3):
//   - solvability of the greedy needs the root's name to be fresh
//     (FreshRootName): a dependency chain demanding the root's own name at
//     a higher version makes the instance unsatisfiable, so "a greedy
//     algorithm suffices" implicitly assumes the root is not upgradable —
//     true of Go's main module, and of the paper's synthetic query root;
//   - determinism ("lock files are unnecessary") holds for the canonical
//     least-visited-set algorithm, which — like Go's — keeps the bounds
//     contributed by superseded versions; the canonical answer is
//     therefore not always pointwise-minimal among valid resolutions.
//
// Theorems are proved in lemmas/MinVersionLemmas.dfy.

include "Core.dfy"
include "Versions.dfy"

module MinVersion {
  import opened Core
  import opened Versions

  // ---------------------------------------------------------------------
  // Approach (1): minimum-bound dependencies.
  // ---------------------------------------------------------------------

  // A dependency min(m, l): name m at version l or above.
  datatype MinDep = MinDep(name: Name, bound: Version)
  type MinDepRel = set<(Package, MinDep)>

  // Definition 3.1.2's side condition: dependers and bound versions exist.
  predicate WfMinDeps(repo: set<Package>, mdeps: MinDepRel) {
    forall e | e in mdeps ::
      e.0 in repo && Package(e.1.name, e.1.bound) in repo
  }

  // §3.3(1)'s replacement for dependency closure:
  //   ∀p ∈ r. p →min (m, l) ⟹ ∃v ≥ l. (m, v) ∈ r.
  predicate MinClosure(mdeps: MinDepRel, r: set<Package>) {
    forall e | e in mdeps && e.0 in r ::
      exists q | q in r :: q.name == e.1.name && e.1.bound <= q.version
  }

  predicate ValidMinResolution(repo: set<Package>, mdeps: MinDepRel,
                               root: Package, r: set<Package>) {
    r <= repo
    && RootInclusion(root, r)
    && MinClosure(mdeps, r)
    && VersionUniqueness(r)
  }

  // No dependency targets the root's name (the root is not upgradable).
  predicate FreshRootName(mdeps: MinDepRel, root: Package) {
    forall e | e in mdeps :: e.1.name != root.name
  }

  // The min-bound calculus is the ≥-fragment of the Version Formula
  // Calculus (§3.2): min(m, l) is the formula m ≥ l.
  function MinToVf(mdeps: MinDepRel): VfDepRel {
    set e | e in mdeps :: (e.0, VfDep(e.1.name, VCmp(Ge, e.1.bound)))
  }

  // ---------------------------------------------------------------------
  // The canonical MVS algorithm: least visited set, then per-name maxima.
  // ---------------------------------------------------------------------

  // A set closed under following minimum bounds.
  predicate MinClosedSet(mdeps: MinDepRel, s: set<Package>) {
    forall e | e in mdeps && e.0 in s :: Package(e.1.name, e.1.bound) in s
  }

  // The visited set: the least bound-closed set containing the root.
  // Leastness makes it unique, which is the determinism behind "lock
  // files are unnecessary under MVS".
  ghost predicate IsMinVisited(mdeps: MinDepRel, root: Package, s: set<Package>) {
    root in s
    && MinClosedSet(mdeps, s)
    && forall w: set<Package> | root in w && MinClosedSet(mdeps, w) :: s <= w
  }

  method MvsVisited(repo: set<Package>, mdeps: MinDepRel, root: Package)
    returns (visited: set<Package>)
    requires WfMinDeps(repo, mdeps)
    requires root in repo
    ensures IsMinVisited(mdeps, root, visited)
    ensures visited <= repo
  {
    visited := {root};
    var work := {root};
    while work != {}
      invariant work <= visited
      invariant root in visited
      invariant visited <= repo
      invariant forall e | e in mdeps && e.0 in visited - work ::
        Package(e.1.name, e.1.bound) in visited
      invariant forall w: set<Package> | root in w && MinClosedSet(mdeps, w) ::
        visited <= w
      decreases |repo - visited|, |work|
    {
      var p :| p in work;
      var targets := set e | e in mdeps && e.0 == p :: Package(e.1.name, e.1.bound);
      var newPkgs := targets - visited;
      visited := visited + newPkgs;
      work := (work - {p}) + newPkgs;
    }
  }

  lemma MaxExists(s: set<Version>)
    requires s != {}
    ensures exists v :: v in s && forall w | w in s :: w <= v
    decreases s
  {
    var x :| x in s;
    if s != {x} {
      MaxExists(s - {x});
      var v :| v in s - {x} && forall w | w in s - {x} :: w <= v;
      assert forall w | w in s :: w == x || w in s - {x};
      if x <= v {
        assert v in s && forall w | w in s :: w <= v;
      } else {
        assert x in s && forall w | w in s :: w <= x;
      }
    }
  }

  function SetMax(s: set<Version>): Version
    requires s != {}
    ensures SetMax(s) in s
    ensures forall w | w in s :: w <= SetMax(s)
  {
    assert exists v :: v in s && forall w | w in s :: w <= v by {
      MaxExists(s);
    }
    var v :| v in s && forall w | w in s :: w <= v;
    v
  }

  function VersionsOfName(s: set<Package>, m: Name): set<Version> {
    set q | q in s && q.name == m :: q.version
  }

  // The maximum visited version of q's name.
  function NameMaxIn(visited: set<Package>, q: Package): Package
    requires q in visited
  {
    assert q.version in VersionsOfName(visited, q.name);
    Package(q.name, SetMax(VersionsOfName(visited, q.name)))
  }

  // The MVS resolution: each visited name at the maximum of its visited
  // versions (the maximum of all minimum bounds).
  function MvsOf(visited: set<Package>): set<Package> {
    set q | q in visited :: NameMaxIn(visited, q)
  }

  // ---------------------------------------------------------------------
  // Approach (2): resolution without version uniqueness.
  // ---------------------------------------------------------------------

  // The core calculus minus Definition 3.1.3(c).
  predicate MultiValid(repo: set<Package>, deps: DepRel, root: Package, r: set<Package>) {
    r <= repo
    && RootInclusion(root, r)
    && DepClosure(deps, r)
  }

  // Greedy resolution by plain reachability, taking every compatible
  // version of every dependency — a graph traversal, as §3.3(2) claims.
  method MultiResolve(repo: set<Package>, deps: DepRel, root: Package)
    returns (r: set<Package>)
    requires WfDeps(repo, deps)
    requires forall e | e in deps :: e.1.versions != {}
    requires root in repo
    ensures MultiValid(repo, deps, root, r)
  {
    r := {root};
    var work := {root};
    while work != {}
      invariant work <= r
      invariant root in r
      invariant r <= repo
      invariant forall e | e in deps && e.0 in r - work ::
        forall u | u in e.1.versions :: Package(e.1.name, u) in r
      decreases |repo - r|, |work|
    {
      var p :| p in work;
      var targets := set e, u | e in deps && e.0 == p && u in e.1.versions ::
        Package(e.1.name, u);
      var newPkgs := targets - r;
      r := r + newPkgs;
      work := (work - {p}) + newPkgs;
    }
    forall e | e in deps && e.0 in r
      ensures exists v :: v in e.1.versions && Package(e.1.name, v) in r
    {
      var u :| u in e.1.versions;
      assert Package(e.1.name, u) in r;
    }
  }

  // The versions of dependency e selected in r, and the canonical (maximal)
  // choice among them — used to relate approach (2) to the Concurrent
  // Package Calculus with identity granularity.
  function SelVers(e: (Package, Dep), r: set<Package>): set<Version> {
    set u | u in e.1.versions && Package(e.1.name, u) in r :: u
  }

  function MaxSelRho(deps: DepRel, r: set<Package>): set<(Package, Package)> {
    set e | e in deps && e.0 in r && SelVers(e, r) != {} ::
      (Package(e.1.name, SetMax(SelVers(e, r))), e.0)
  }
}
