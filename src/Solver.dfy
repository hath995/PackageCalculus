// Solver.dfy — An exhaustive, verified resolver for the core calculus.
//
// DependencyResolution is NP-complete (Theorem 3.1.4), so we enumerate — but
// LAZILY: AllResolutions walks include/exclude decisions depth-first
// (DfsResolutions), so memory is the recursion depth plus the (typically tiny)
// result set. The previous implementation materialised Subsets(repo) — all
// 2^|repo| subsets simultaneously, as a set-of-sets — which exhausted RAM
// around twenty packages; time stays exponential (the problem is NP-complete)
// but the memory wall is gone. The postcondition of AllResolutions
// characterises S(D, root) exactly: a set is returned iff it is a valid
// resolution.
//
// Subsets survives as GHOST vocabulary: DfsResolutions' postcondition is
// stated against it, and SubsetsComplete justifies AllResolutions' final iff.

include "Core.dfy"

module Solver {
  import opened Core

  function ToSet<T>(xs: seq<T>): set<T> {
    set x | x in xs
  }

  // All subsets of the elements of xs. Spec-only: nothing executes this any
  // more (materialising it is exactly the memory wall DfsResolutions removes).
  ghost function Subsets<T>(xs: seq<T>): set<set<T>>
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

  // Depth-first include/exclude enumeration: exactly the valid resolutions of
  // the form chosen + sub for sub a subset of xs's elements. Never builds the
  // powerset — live memory is the recursion spine plus the accumulated VALID
  // resolutions (for real instances, a handful), where Subsets(xs) held all
  // 2^|xs| candidates at once.
  method DfsResolutions(xs: seq<Package>, chosen: set<Package>,
                        repo: set<Package>, deps: DepRel, root: Package)
    returns (rs: set<set<Package>>)
    ensures rs == set sub | sub in Subsets(xs) && ValidResolution(repo, deps, root, chosen + sub)
                          :: chosen + sub
    decreases |xs|
  {
    if |xs| == 0 {
      assert Subsets(xs) == {{}};
      assert chosen + {} == chosen;
      if ValidResolution(repo, deps, root, chosen) {
        rs := {chosen};
      } else {
        rs := {};
      }
    } else {
      var x := xs[0];
      var without := DfsResolutions(xs[1..], chosen, repo, deps, root);
      var withX := DfsResolutions(xs[1..], chosen + {x}, repo, deps, root);
      rs := without + withX;

      ghost var rest := Subsets(xs[1..]);
      assert Subsets(xs) == rest + set s | s in rest :: s + {x};
      ghost var want := set sub | sub in Subsets(xs) && ValidResolution(repo, deps, root, chosen + sub)
                                :: chosen + sub;

      forall r | r in rs
        ensures r in want
      {
        if r in without {
          var sub :| sub in rest && r == chosen + sub && ValidResolution(repo, deps, root, chosen + sub);
        } else {
          var s :| s in rest && r == (chosen + {x}) + s && ValidResolution(repo, deps, root, (chosen + {x}) + s);
          assert (chosen + {x}) + s == chosen + (s + {x});
          assert s + {x} in Subsets(xs);
        }
      }
      forall r | r in want
        ensures r in rs
      {
        var sub :| sub in Subsets(xs) && r == chosen + sub && ValidResolution(repo, deps, root, chosen + sub);
        if sub in rest {
          assert r in without;
        } else {
          var s :| s in rest && sub == s + {x};
          assert chosen + sub == (chosen + {x}) + s;
          assert r in withX;
        }
      }
      assert rs == want;
    }
  }

  // Computes S(D, root) over repo, exactly.
  method AllResolutions(repo: set<Package>, deps: DepRel, root: Package)
    returns (rs: set<set<Package>>)
    ensures forall r :: r in rs <==> ValidResolution(repo, deps, root, r)
  {
    var xs := SetToSeq(repo);
    rs := DfsResolutions(xs, {}, repo, deps, root);
    forall r | ValidResolution(repo, deps, root, r)
      ensures r in rs
    {
      SubsetsComplete(xs, r);
      assert {} + r == r;
    }
    forall r | r in rs
      ensures ValidResolution(repo, deps, root, r)
    {
      var sub :| sub in Subsets(xs) && r == {} + sub && ValidResolution(repo, deps, root, {} + sub);
    }
  }
}
