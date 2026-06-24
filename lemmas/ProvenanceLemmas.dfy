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

  // ---- combining import sets across dependers: the join model -------------
  //
  //   JoinLeResolver                  — the join is the LEAST version that can
  //                                     resolve the union: any resolver >= it.
  //   CombinedSatisfiableIffResolves  — satisfiability IS "some version resolves
  //                                     the whole union", and the witness is the
  //                                     join. So cross-depender resolution is a
  //                                     single-point check at the join.
  //   LatestAnchoredSatisfiable       — a lone latest-anchored import set is
  //                                     always satisfiable: the join model
  //                                     strictly extends the window model and
  //                                     only reports conflict across anchors.

  // The join is the least version that can satisfy U: any resolver dominates it.
  // The max-era object is in its era only at versions >= its era start, and a
  // version's last_changed never exceeds the version itself.
  lemma JoinLeResolver(h: History, U: set<EraReq>, v: Version)
    requires WfHistory(h) && WfReq(h, U) && U != {}
    requires ValidVersion(h, v) && ResolvesAt(h, U, v)
    ensures Join(h, U) <= v
  {
    var m := Join(h, U);
    assert m in ReqEras(U);
    assert exists r :: r in U && r.1 == m;
    var rstar :| rstar in U && rstar.1 == m;
    assert LastBreak(h, rstar.0, v) == rstar.1;   // ResolvesAt at v
    // LastBreak(h, rstar.0, v) <= v, and it equals m.
  }

  // Satisfiability of the requirement union is exactly "some released version
  // resolves the whole union", with the join as witness. So combined resolution
  // across dependers reduces to a single-point evaluation at the join: no search.
  lemma CombinedSatisfiableIffResolves(h: History, U: set<EraReq>)
    requires WfHistory(h) && WfReq(h, U)
    ensures CombinedSatisfiable(h, U)
        <==> (exists v :: ValidVersion(h, v) && ResolvesAt(h, U, v))
  {
    // (==>) the join (or, for the empty union, the latest version) resolves U.
    if CombinedSatisfiable(h, U) {
      if U == {} {
        assert ValidVersion(h, Latest(h)) && ResolvesAt(h, U, Latest(h));
      } else {
        assert ValidVersion(h, Join(h, U)) && ResolvesAt(h, U, Join(h, U));
      }
    }
    // (<==) any resolver v gives consistency (clause 1), and pulling each object
    // back from v to the join keeps it in the same era (StableEra).
    if exists v :: ValidVersion(h, v) && ResolvesAt(h, U, v) {
      var v :| ValidVersion(h, v) && ResolvesAt(h, U, v);
      forall a, b | a in U && b in U && a.0 == b.0
        ensures a.1 == b.1
      {
        assert LastBreak(h, a.0, v) == a.1;
        assert LastBreak(h, b.0, v) == b.1;
      }
      assert SingleTagged(U);
      if U != {} {
        var m := Join(h, U);
        JoinLeResolver(h, U, v);
        forall r | r in U
          ensures Present(h, r.0, m) && LastBreak(h, r.0, m) == r.1
        {
          assert LastBreak(h, r.0, v) == r.1 <= m <= v;
          StableEra(h, r.0, v, m);
        }
        assert ResolvesAt(h, U, m);
      }
      assert CombinedSatisfiable(h, U);
    }
  }

  // The latest-anchored import set as a requirement union: import set s, each
  // object pinned to the form it has at the latest version.
  function LatestAnchored(h: History, s: set<Obj>): set<EraReq>
    requires WfHistory(h) && ImportsPresentAtLatest(h, s)
  {
    set o | o in s :: (o, LastBreak(h, o, Latest(h)))
  }

  // Consistency with the window model: a single depender's latest-anchored
  // imports are ALWAYS satisfiable, resolved by the latest version. So the join
  // model strictly extends the window model — it never reports a conflict for a
  // lone latest-anchored set, only when eras come from different anchors.
  lemma LatestAnchoredSatisfiable(h: History, s: set<Obj>)
    requires WfHistory(h) && ImportsPresentAtLatest(h, s)
    ensures WfReq(h, LatestAnchored(h, s))
    ensures CombinedSatisfiable(h, LatestAnchored(h, s))
  {
    var U := LatestAnchored(h, s);
    forall r | r in U
      ensures ValidVersion(h, r.1) && Present(h, r.0, r.1) && BrokeAt(h, r.0, r.1)
    {
      var o :| o in s && r == (o, LastBreak(h, o, Latest(h)));
      // LastBreak ensures BrokeAt & ValidVersion; broke <= objs gives Present.
      assert h.releases[r.1].broke <= h.releases[r.1].objs;
    }
    assert WfReq(h, U);
    forall r | r in U
      ensures Present(h, r.0, Latest(h)) && LastBreak(h, r.0, Latest(h)) == r.1
    {
      var o :| o in s && r == (o, LastBreak(h, o, Latest(h)));
    }
    assert ResolvesAt(h, U, Latest(h));
    CombinedSatisfiableIffResolves(h, U);
  }

  // ---- deriving the requirement union from a dependency set ---------------
  //
  //   AnchoredImportWfReq / UnionReqWfReq  — anchored imports, and unions of
  //                                          them, are well-formed requirement
  //                                          sets: the join machinery applies.
  //   SingleDependerSatisfiable            — one depender is always satisfiable
  //                                          on its own (resolved at its anchor);
  //                                          LatestAnchoredSatisfiable is the
  //                                          anchor = latest special case.
  //   GraphResolves                        — satisfiability of a whole dependency
  //                                          set ⇔ some version resolves it.
  //   DependerSatisfiedAtJoin              — at a resolving version, every
  //                                          depender sees each import in the
  //                                          same form it had at its anchor.

  // An anchored import is a well-formed requirement set: each (o, last_changed)
  // names an era at which o exists and broke.
  lemma AnchoredImportWfReq(h: History, d: Depender)
    requires WfHistory(h) && WfDepender(h, d)
    ensures WfReq(h, AnchoredImport(h, d))
  {
    forall r | r in AnchoredImport(h, d)
      ensures ValidVersion(h, r.1) && Present(h, r.0, r.1) && BrokeAt(h, r.0, r.1)
    {
      var o :| o in d.imports && r == (o, LastBreak(h, o, d.anchor));
      assert h.releases[r.1].broke <= h.releases[r.1].objs;   // broke <= objs ⇒ Present
    }
  }

  // A union of anchored imports is well-formed: WfReq is a per-element property,
  // and every element comes from some depender's (well-formed) anchored import.
  lemma UnionReqWfReq(h: History, ds: set<Depender>)
    requires WfHistory(h) && WfDependers(h, ds)
    ensures WfReq(h, UnionReq(h, ds))
  {
    forall r | r in UnionReq(h, ds)
      ensures ValidVersion(h, r.1) && Present(h, r.0, r.1) && BrokeAt(h, r.0, r.1)
    {
      var d :| d in ds && r in AnchoredImport(h, d);
      AnchoredImportWfReq(h, d);
    }
  }

  // One depender on its own always resolves — at its own anchor, where each
  // import is by construction in exactly its required era.
  lemma SingleDependerSatisfiable(h: History, d: Depender)
    requires WfHistory(h) && WfDepender(h, d)
    ensures WfReq(h, AnchoredImport(h, d))
    ensures CombinedSatisfiable(h, AnchoredImport(h, d))
  {
    AnchoredImportWfReq(h, d);
    var U := AnchoredImport(h, d);
    forall r | r in U
      ensures Present(h, r.0, d.anchor) && LastBreak(h, r.0, d.anchor) == r.1
    {
      var o :| o in d.imports && r == (o, LastBreak(h, o, d.anchor));
    }
    assert ResolvesAt(h, U, d.anchor);
    CombinedSatisfiableIffResolves(h, U);
  }

  // The dispatchable check over a dependency set: the union is well-formed, and
  // it is satisfiable iff some library version resolves every depender at once —
  // with the join as witness. This is the single per-library check the resolver
  // runs over the whole graph.
  lemma GraphResolves(h: History, ds: set<Depender>)
    requires WfHistory(h) && WfDependers(h, ds)
    ensures WfReq(h, UnionReq(h, ds))
    ensures CombinedSatisfiable(h, UnionReq(h, ds))
        <==> (exists v :: ValidVersion(h, v) && ResolvesAt(h, UnionReq(h, ds), v))
  {
    UnionReqWfReq(h, ds);
    CombinedSatisfiableIffResolves(h, UnionReq(h, ds));
  }

  // At a version that resolves the whole set, each depender sees every one of
  // its imports in the SAME form it had at that depender's anchor — closing the
  // loop back to the per-object compatibility notion (SameForm) of the window
  // model. So a graph resolution is a genuine simultaneous compatibility point.
  lemma DependerSatisfiedAtJoin(h: History, ds: set<Depender>, d: Depender, v: Version)
    requires WfHistory(h) && WfDependers(h, ds) && d in ds
    requires ValidVersion(h, v) && ResolvesAt(h, UnionReq(h, ds), v)
    ensures forall o | o in d.imports :: SameForm(h, o, d.anchor, v)
  {
    forall o | o in d.imports
      ensures SameForm(h, o, d.anchor, v)
    {
      var r := (o, LastBreak(h, o, d.anchor));
      assert r in AnchoredImport(h, d);
      assert r in UnionReq(h, ds);              // d in ds
      assert LastBreak(h, o, v) == r.1;         // ResolvesAt at v
    }
  }
}
