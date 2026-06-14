// ProvenanceLemmas.dfy — theorems for the import-set compatibility model of
// src/Provenance.dfy.
//
//   StableEra            — within an object's breaking-free era, presence and
//                          last_changed are constant (the structural fact).
//   WindowIsInterval     — the compatible window for an import set is exactly
//                          the interval [MinSupport, latest]: a version w is
//                          import-compatible iff MinSupport <= w.
//   BaselineInWindow     — the latest version is always in the window.
//   ImportMonotone       — a larger import set gives a window no wider (using
//                          more objects can only narrow compatibility).
//   ClassRefinement      — the coarse compatibility class is the window for the
//                          FULL object set; per-import windows refine it.
//   WindowAsFormula      — the window is exactly the §3.2 version formula
//                          `>= MinSupport && <= latest`, so windowed resolution
//                          is ValidVfResolution and reduces to the core
//                          (Theorem 3.2.7).

include "../src/Provenance.dfy"

module ProvenanceLemmas {
  import opened Core
  import opened Versions
  import opened Provenance

  // Within object o's current breaking-free era — every u between its
  // last_changed and v — o is present and has the same last_changed as at v.
  lemma StableEra(h: History, o: Obj, v: Version, u: Version)
    requires WfHistory(h) && ValidVersion(h, v) && Present(h, o, v)
    requires LastBreak(h, o, v) <= u <= v
    ensures ValidVersion(h, u) && Present(h, o, u)
    ensures LastBreak(h, o, u) == LastBreak(h, o, v)
    decreases v - u
  {
    if u != v {
      // lb <= u < v, so o did not break at v (else last_changed would be v).
      assert !BrokeAt(h, o, v);
      PresentPrevWhenUnbroken(h, o, v);
      assert LastBreak(h, o, v) == LastBreak(h, o, v - 1);
      StableEra(h, o, v - 1, u);
    }
  }

  // MinSupport dominates every imported object's last_changed.
  lemma MinSupportGeEach(h: History, s: set<Obj>, o: Obj)
    requires WfHistory(h) && ImportsPresentAtLatest(h, s) && o in s
    ensures LastBreak(h, o, Latest(h)) <= MinSupport(h, s)
  {
    var breaks := ImportBreaks(h, s);
    assert LastBreak(h, o, Latest(h)) in breaks;
  }

  // MinSupport is achieved by some imported object's last_changed.
  lemma MinSupportWitness(h: History, s: set<Obj>)
    requires WfHistory(h) && ImportsPresentAtLatest(h, s) && s != {}
    ensures exists o :: o in s && MinSupport(h, s) == LastBreak(h, o, Latest(h))
  {
    var breaks := ImportBreaks(h, s);
    var o0 :| o0 in s;
    assert LastBreak(h, o0, Latest(h)) in breaks;       // breaks != {}
    assert MinSupport(h, s) == SetMax(breaks);
    assert SetMax(breaks) in breaks;
  }

  // The compatible window for an import set is exactly the interval
  // [MinSupport, latest]: w is import-compatible iff MinSupport <= w (the
  // upper bound latest is implied by w being a released version).
  lemma WindowIsInterval(h: History, s: set<Obj>, w: Version)
    requires WfHistory(h) && ValidVersion(h, w) && ImportsPresentAtLatest(h, s)
    ensures InWindow(h, s, w) <==> MinSupport(h, s) <= w
  {
    if MinSupport(h, s) <= w {
      forall o | o in s ensures SameForm(h, o, Latest(h), w) {
        MinSupportGeEach(h, s, o);
        StableEra(h, o, Latest(h), w);
      }
    } else if s != {} {
      MinSupportWitness(h, s);
      var o :| o in s && MinSupport(h, s) == LastBreak(h, o, Latest(h));
      if InWindow(h, s, w) {
        assert SameForm(h, o, Latest(h), w);
        assert LastBreak(h, o, w) == LastBreak(h, o, Latest(h));
        assert LastBreak(h, o, w) <= w;
        assert false;
      }
    }
  }

  // The latest version is always import-compatible (resolve against it).
  lemma BaselineInWindow(h: History, s: set<Obj>)
    requires WfHistory(h) && ImportsPresentAtLatest(h, s)
    ensures InWindow(h, s, Latest(h))
  {
    WindowIsInterval(h, s, Latest(h));
  }

  // ---- monotonicity and the class as the full-import window ---------------

  lemma SetMaxMono(a: set<Version>, b: set<Version>)
    requires a <= b && a != {}
    ensures SetMax(a) <= SetMax(b)
  {
    assert b != {};
    assert SetMax(a) in b;
  }

  lemma MinSupportMono(h: History, s: set<Obj>, t: set<Obj>)
    requires WfHistory(h) && ImportsPresentAtLatest(h, t) && s <= t
    ensures ImportsPresentAtLatest(h, s)
    ensures MinSupport(h, s) <= MinSupport(h, t)
  {
    assert ImportsPresentAtLatest(h, s);
    var bs := ImportBreaks(h, s);
    var bt := ImportBreaks(h, t);
    assert bs <= bt;
    if bs != {} {
      SetMaxMono(bs, bt);
    }
  }

  // A larger import set yields a window no wider: class-compatibility (using
  // everything) implies import-compatibility, never the reverse.
  lemma ImportMonotone(h: History, s: set<Obj>, t: set<Obj>, w: Version)
    requires WfHistory(h) && ValidVersion(h, w) && ImportsPresentAtLatest(h, t) && s <= t
    ensures ImportsPresentAtLatest(h, s)
    ensures InWindow(h, t, w) ==> InWindow(h, s, w)
  {
    MinSupportMono(h, s, t);
    WindowIsInterval(h, s, w);
    WindowIsInterval(h, t, w);
  }

  // The objects exported at the latest version — the "everything" import set.
  function AllObjs(h: History): set<Obj>
    requires WfHistory(h)
  {
    h.releases[Latest(h)].objs
  }

  // The coarse compatibility class is the window for the FULL object set:
  // class-compatible ⇒ import-compatible for any subset, and the per-import
  // window starts no later than the class window (MinSupport over everything =
  // the last version *anything* broke = the class boundary). So per-import
  // windows refine — never narrow below — the class.
  lemma ClassRefinement(h: History, s: set<Obj>, w: Version)
    requires WfHistory(h) && ValidVersion(h, w) && s <= AllObjs(h)
    ensures ImportsPresentAtLatest(h, AllObjs(h)) && ImportsPresentAtLatest(h, s)
    ensures InWindow(h, AllObjs(h), w) ==> InWindow(h, s, w)
    ensures MinSupport(h, s) <= MinSupport(h, AllObjs(h))
  {
    assert ImportsPresentAtLatest(h, AllObjs(h));
    ImportMonotone(h, s, AllObjs(h), w);
    MinSupportMono(h, s, AllObjs(h));
  }

  // ---- the window is a §3.2 version formula -------------------------------

  // Evaluating the window formula over any version universe yields exactly the
  // interval [MinSupport, latest] within it.
  lemma WindowAsFormula(h: History, s: set<Obj>, universe: set<Version>)
    requires WfHistory(h) && ImportsPresentAtLatest(h, s)
    ensures Versions.Eval(WindowFormula(h, s), universe)
         == set w | w in universe && MinSupport(h, s) <= w <= Latest(h)
  {
  }

  // The payoff: over the released-version universe, evaluating the window
  // formula yields exactly the import-compatible versions. So a windowed
  // dependency `(name, WindowFormula)` is an ordinary §3.2 VfDep whose
  // semantics is the compatibility window — windowed resolution IS
  // ValidVfResolution and reduces to the core via Theorem 3.2.7, with no new
  // resolver. The novelty is the *derivation* of the formula from per-object
  // provenance (the theorems above), not the resolution.
  lemma WindowMatchesEval(h: History, s: set<Obj>, universe: set<Version>)
    requires WfHistory(h) && ImportsPresentAtLatest(h, s)
    requires forall v :: v in universe <==> ValidVersion(h, v)
    ensures Versions.Eval(WindowFormula(h, s), universe)
         == set w | w in universe && InWindow(h, s, w)
  {
    WindowAsFormula(h, s, universe);
    forall w | w in universe
      ensures (MinSupport(h, s) <= w <= Latest(h)) <==> InWindow(h, s, w)
    {
      WindowIsInterval(h, s, w);
    }
  }
}
