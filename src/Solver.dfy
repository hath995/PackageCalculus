// Solver.dfy — An exhaustive, verified resolver for the core calculus.
//
// DependencyResolution is NP-complete (Theorem 3.1.4), so for the small
// instances in tests/ we simply enumerate all subsets of the repository and
// keep the valid ones. The postcondition of AllResolutions characterises
// S(D, root) exactly: a set is returned iff it is a valid resolution.
//
// The two lemmas about Subsets are implementation plumbing (they justify
// AllResolutions' postcondition); the paper's theorems live in lemmas/.

include "Core.dfy"

module Solver {
  import opened Core

  function ToSet<T>(xs: seq<T>): set<T> {
    set x | x in xs
  }

  // All subsets of the elements of xs.
  function Subsets<T(==)>(xs: seq<T>): set<set<T>>
    decreases |xs|
  {
    if |xs| == 0 then {{}}
    else
      var rest := Subsets(xs[1..]);
      rest + set s | s in rest :: s + {xs[0]}
  }

  lemma SubsetsComplete<T>(xs: seq<T>, sub: set<T>)
    requires sub <= ToSet(xs)
    ensures sub in Subsets(xs)
    decreases |xs|
  {
    if |xs| == 0 {
      assert sub == {};
    } else {
      var x := xs[0];
      assert xs == [x] + xs[1..];
      assert forall y :: y in ToSet(xs) ==> y == x || y in ToSet(xs[1..]);
      if x in sub {
        SubsetsComplete(xs[1..], sub - {x});
        assert sub == (sub - {x}) + {x};
      } else {
        SubsetsComplete(xs[1..], sub);
      }
    }
  }

  method SetToSeq<T(==)>(s: set<T>) returns (xs: seq<T>)
    ensures ToSet(xs) == s
  {
    xs := [];
    var rest := s;
    while rest != {}
      invariant ToSet(xs) + rest == s
      decreases |rest|
    {
      var x :| x in rest;
      xs := xs + [x];
      rest := rest - {x};
    }
  }

  // Computes S(D, root) over repo, exactly.
  method AllResolutions(repo: set<Package>, deps: DepRel, root: Package)
    returns (rs: set<set<Package>>)
    ensures forall r :: r in rs <==> ValidResolution(repo, deps, root, r)
  {
    var xs := SetToSeq(repo);
    var subs := Subsets(xs);
    rs := set r | r in subs && ValidResolution(repo, deps, root, r);
    forall r | ValidResolution(repo, deps, root, r)
      ensures r in subs
    {
      SubsetsComplete(xs, r);
    }
  }
}
