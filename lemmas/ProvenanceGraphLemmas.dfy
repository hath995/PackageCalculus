// ProvenanceGraphLemmas.dfy — theorems for the multi-library graph model of
// src/ProvenanceGraph.dfy.
//
//   EdgeAnchorSat     — the anchor version always satisfies its own edge, so
//                       every edge's satisfying set is non-empty.
//   EdgeWindowConvex  — that satisfying set is an INTERVAL: the anchored window
//                       generalised off the latest version. Its upper bound is
//                       the next break of an imported object, which may lie
//                       strictly below the latest version — the cross-anchor
//                       capability the latest-anchored window lacked.
//   GraphClauseOne    — clause 1 lifted to the graph: if a resolution has two
//                       selected packages whose edges demand a shared object of
//                       a common target in two different eras, no resolution
//                       exists. The transitive analogue of SingleTagged.

include "../src/ProvenanceGraph.dfy"
include "ProvenanceLemmas.dfy"
include "VersionsLemmas.dfy"

module ProvenanceGraphLemmas {
  import opened Core
  import opened Versions
  import opened Provenance
  import opened ProvenanceGraph
  import opened ProvenanceLemmas
  import opened VersionsLemmas

  // The anchor itself satisfies the edge: at v == a every object is trivially in
  // its anchor era. So no edge is vacuously unsatisfiable.
  lemma EdgeAnchorSat(h: History, a: Version, s: set<Obj>)
    requires WfHistory(h) && ValidVersion(h, a)
    requires forall o | o in s :: Present(h, o, a)
    ensures EdgeSatH(h, a, s, a)
  {}

  // The satisfying set of an edge is an interval: if v1 and v2 satisfy it, so
  // does every version between. Each imported object is in its anchor era at both
  // ends — its last_changed equals the anchor's — so by StableEra it stays in
  // that era throughout. This is the latest-anchored window generalised to an
  // arbitrary anchor: the upper bound is the next break of an imported object,
  // and so may fall strictly below the latest version (the case the
  // latest-anchored window structurally could not express).
  lemma EdgeWindowConvex(h: History, a: Version, s: set<Obj>, v1: Version, v2: Version, w: Version)
    requires WfHistory(h)
    requires EdgeSatH(h, a, s, v1) && EdgeSatH(h, a, s, v2)
    requires v1 <= w <= v2
    ensures ValidVersion(h, w) && EdgeSatH(h, a, s, w)
  {
    assert ValidVersion(h, w);   // 0 <= v1 <= w <= v2 < |releases|
    forall o | o in s
      ensures Present(h, o, w) && LastBreak(h, o, w) == LastBreak(h, o, a)
    {
      // last_changed at v2 equals the anchor's; and it is <= v1 <= w <= v2, so
      // StableEra carries the era (and presence) back from v2 to w.
      assert LastBreak(h, o, v1) <= v1;
      StableEra(h, o, v2, w);
    }
  }

  // Clause 1, lifted to the graph. If a valid resolution has two selected
  // packages (n1, n2) whose edges (e1, e2) both target library t and both import
  // object o, but anchor o in DIFFERENT eras, no such resolution can exist: the
  // single selected version sel[t] would have to show o in both eras at once.
  // This is the transitive form of Provenance.SingleTagged — the reason a
  // cross-package era conflict is unsatisfiable across the whole graph.
  lemma GraphClauseOne(u: Universe, root: Name, sel: map<Name, Version>,
                       n1: Name, e1: Edge, n2: Name, e2: Edge, t: Name, o: Obj)
    requires WfUniverse(u) && ValidGraphResolution(u, root, sel)
    requires n1 in sel && (n1, sel[n1]) in u.edges && e1 in u.edges[(n1, sel[n1])]
    requires n2 in sel && (n2, sel[n2]) in u.edges && e2 in u.edges[(n2, sel[n2])]
    requires e1.target == t && e2.target == t && t in u.hist
    requires o in e1.imports && o in e2.imports
    requires LastBreak(u.hist[t], o, e1.anchor) != LastBreak(u.hist[t], o, e2.anchor)
    ensures false
  {
    var h := u.hist[t];
    // Both edges are satisfied by the single selected version sel[t].
    assert EdgeSatH(h, e1.anchor, e1.imports, sel[t]);
    assert EdgeSatH(h, e2.anchor, e2.imports, sel[t]);
    // So o's era at sel[t] equals BOTH anchors' eras — contradiction.
    assert LastBreak(h, o, sel[t]) == LastBreak(h, o, e1.anchor);
    assert LastBreak(h, o, sel[t]) == LastBreak(h, o, e2.anchor);
  }

  // ---- each edge denotes a §3.2 version formula ---------------------------

  // EdgeJoin is the least satisfying version: it satisfies the edge, and no
  // smaller version does. (Going DOWN from the anchor, StableEra keeps every
  // import in its anchor era as far back as the join; below the join some import
  // has not yet reached that era.)
  lemma EdgeJoinIsMin(h: History, a: Version, s: set<Obj>)
    requires WfEdge(h, a, s)
    ensures EdgeSatH(h, a, s, EdgeJoin(h, a, s))
    ensures forall v: Version | v < |h.releases| && EdgeSatH(h, a, s, v) :: EdgeJoin(h, a, s) <= v
  {
    var lo := EdgeJoin(h, a, s);
    if s != {} {
      var imgs := set o | o in s :: LastBreak(h, o, a);
      assert lo == SetMax(imgs);
      forall x | x in imgs ensures x <= a { var o :| o in s && x == LastBreak(h, o, a); }
      assert lo <= a;
      forall o | o in s
        ensures Present(h, o, lo) && LastBreak(h, o, lo) == LastBreak(h, o, a)
      {
        assert LastBreak(h, o, a) in imgs;       // so LastBreak(h,o,a) <= lo
        StableEra(h, o, a, lo);                  // carries the era from a down to lo
      }
    }
    forall v: Version | v < |h.releases| && EdgeSatH(h, a, s, v)
      ensures lo <= v
    {
      if s != {} {
        var imgs := set o | o in s :: LastBreak(h, o, a);
        forall x | x in imgs ensures x <= v {
          var o :| o in s && x == LastBreak(h, o, a);
          assert LastBreak(h, o, v) == LastBreak(h, o, a);   // EdgeSatH at v
        }
        assert SetMax(imgs) <= v;                // SetMax in imgs, all of imgs <= v
      }
    }
  }

  // The satisfying set is exactly the interval [EdgeJoin, EdgeHi].
  lemma EdgeVersionsInterval(h: History, a: Version, s: set<Obj>, v: Version)
    requires WfEdge(h, a, s) && v < |h.releases|
    ensures EdgeSatH(h, a, s, v) <==> (EdgeJoin(h, a, s) <= v <= EdgeHi(h, a, s))
  {
    EdgeJoinIsMin(h, a, s);
    var lo := EdgeJoin(h, a, s);
    var hi := EdgeHi(h, a, s);
    assert hi in EdgeVersions(h, a, s);          // EdgeHi postcondition
    assert EdgeSatH(h, a, s, hi) && hi < |h.releases|;
    if lo <= v <= hi {
      EdgeWindowConvex(h, a, s, lo, hi, v);
    }
    if EdgeSatH(h, a, s, v) {
      assert v in EdgeVersions(h, a, s);         // v <= SetMax = hi
    }
  }

  // The payoff: over the target's version universe, the edge formula's Eval is
  // exactly the edge's satisfying set. So a provenance edge IS an ordinary §3.2
  // version-formula dependency — and graph resolution reduces, edge by edge, to
  // the Version Formula Calculus (and thence to the core via Theorem 3.2.7).
  lemma EdgeFormulaEval(h: History, a: Version, s: set<Obj>, universe: set<Version>)
    requires WfEdge(h, a, s)
    requires forall v: Version :: v in universe <==> v < |h.releases|
    ensures Eval(EdgeFormula(h, a, s), universe)
         == set v | v in universe && EdgeSatH(h, a, s, v)
  {
    forall u | u in universe
      ensures u in Eval(EdgeFormula(h, a, s), universe) <==> EdgeSatH(h, a, s, u)
    {
      EdgeVersionsInterval(h, a, s, u);
    }
  }

  // ---- reduction to the Version Formula Calculus --------------------------

  lemma VRangeMem(k: nat, v: Version)
    ensures v in VRange(k) <==> v < k
  {
    if k > 0 { VRangeMem(k - 1, v); }
  }

  // The version universe of a target in the reduced repository is exactly its
  // released versions — matching EdgeFormulaEval's universe hypothesis.
  lemma VersionsOfRepo(u: Universe, t: Name)
    requires WfUniverse(u) && t in u.hist
    ensures forall v: Version :: v in VersionsOf(Repo(u), t) <==> v < |u.hist[t].releases|
  {
    forall v: Version ensures v in VersionsOf(Repo(u), t) <==> v < |u.hist[t].releases| {
      VRangeMem(|u.hist[t].releases|, v);
      assert Package(t, v) in Repo(u) <==> v in VRange(|u.hist[t].releases|);
      assert v in VersionsOf(Repo(u), t) <==> Package(t, v) in Repo(u);
    }
  }

  // A package is in the selection set iff the selection maps its name to its
  // version.
  lemma SelMem(sel: map<Name, Version>, p: Package)
    ensures p in SelToSet(sel) <==> (p.name in sel && sel[p.name] == p.version)
  {}

  // A package is in the reduced repository iff it is a released version of an
  // existing library.
  lemma RepoMem(u: Universe, p: Package)
    requires WfUniverse(u)
    ensures p in Repo(u) <==> (p.name in u.hist && p.version < |u.hist[p.name].releases|)
  {
    if p.name in u.hist { VRangeMem(|u.hist[p.name].releases|, p.version); }
  }

  // A well-formed edge of the graph yields a well-formed edge for the formula.
  lemma EdgeWf(u: Universe, k: (Name, Version), e: Edge)
    requires WfGraph(u) && k in u.edges && e in u.edges[k]
    ensures e.target in u.hist && WfEdge(u.hist[e.target], e.anchor, e.imports)
  {}

  // The heart of the reduction: formula dependency-closure of the reduced
  // problem over a selection set is exactly the in-form edge condition. Each
  // entry of ToVfDeps is an edge of some selected (library,version); its only
  // satisfying package in the selection set is the selected version of its
  // target, and that version lies in the formula's Eval iff it satisfies the
  // edge (EdgeFormulaEval).
  lemma ClosureIffEdgeCond(u: Universe, sel: map<Name, Version>)
    requires WfGraph(u)
    ensures VfDepClosure(Repo(u), ToVfDeps(u), SelToSet(sel)) <==> EdgeCond(u, sel)
  {
    var repo := Repo(u);
    var vdeps := ToVfDeps(u);
    var r := SelToSet(sel);

    if VfDepClosure(repo, vdeps, r) {
      forall n | n in sel && (n, sel[n]) in u.edges
        ensures forall e | e in u.edges[(n, sel[n])] ::
                  e.target in sel && e.target in u.hist
                  && EdgeSatH(u.hist[e.target], e.anchor, e.imports, sel[e.target])
      {
        forall e | e in u.edges[(n, sel[n])]
          ensures e.target in sel && e.target in u.hist
               && EdgeSatH(u.hist[e.target], e.anchor, e.imports, sel[e.target])
        {
          EdgeWf(u, (n, sel[n]), e);
          var h := u.hist[e.target];
          var ed := (Package(n, sel[n]), VfDep(e.target, EdgeFormula(h, e.anchor, e.imports)));
          assert ed in vdeps;
          SelMem(sel, Package(n, sel[n]));
          assert ed.0 in r;                          // n in sel
          var w :| w in Eval(ed.1.formula, VersionsOf(repo, e.target))
                && Package(e.target, w) in r;
          SelMem(sel, Package(e.target, w));
          assert e.target in sel && sel[e.target] == w;
          VersionsOfRepo(u, e.target);
          EdgeFormulaEval(h, e.anchor, e.imports, VersionsOf(repo, e.target));
        }
      }
      assert EdgeCond(u, sel);
    }

    if EdgeCond(u, sel) {
      forall ed | ed in vdeps && ed.0 in r
        ensures exists w :: w in Eval(ed.1.formula, VersionsOf(repo, ed.1.name))
                         && Package(ed.1.name, w) in r
      {
        var k, e :| k in u.edges && e in u.edges[k]
          && ed == (Package(k.0, k.1), VfDep(e.target, EdgeFormula(u.hist[e.target], e.anchor, e.imports)));
        EdgeWf(u, k, e);
        var h := u.hist[e.target];
        SelMem(sel, ed.0);
        assert k.0 in sel && sel[k.0] == k.1;        // ed.0 in r
        // k == (k.0, sel[k.0]) is an edge key, so EdgeCond applies to e.
        assert e.target in sel
            && EdgeSatH(h, e.anchor, e.imports, sel[e.target]);
        var w := sel[e.target];
        SelMem(sel, Package(e.target, w));
        assert Package(e.target, w) in r;
        VersionsOfRepo(u, e.target);
        EdgeFormulaEval(h, e.anchor, e.imports, VersionsOf(repo, e.target));
        assert w in Eval(ed.1.formula, VersionsOf(repo, ed.1.name));
      }
      assert VfDepClosure(repo, vdeps, r);
    }
  }

  // The reduction is faithful: graph resolution is exactly ValidVfResolution
  // over the reduced repository and dependencies.
  lemma GraphReducesToVf(u: Universe, rootName: Name, sel: map<Name, Version>)
    requires WfGraph(u) && rootName in sel
    ensures ValidGraphResolution(u, rootName, sel)
        <==> ValidVfResolution(Repo(u), ToVfDeps(u), Package(rootName, sel[rootName]), SelToSet(sel))
  {
    var repo := Repo(u);
    var r := SelToSet(sel);
    var rootPkg := Package(rootName, sel[rootName]);

    // r <= repo  <==>  every selected library/version exists.
    forall p | p in r
      ensures p in repo <==> (p.name in u.hist && ValidVersion(u.hist[p.name], p.version))
    {
      SelMem(sel, p);
      RepoMem(u, p);
    }
    assert (r <= repo) <==> (forall n | n in sel :: n in u.hist && ValidVersion(u.hist[n], sel[n])) by {
      forall n | n in sel ensures Package(n, sel[n]) in r { SelMem(sel, Package(n, sel[n])); }
      forall n | n in sel ensures (Package(n, sel[n]) in repo
                  <==> (n in u.hist && ValidVersion(u.hist[n], sel[n]))) {
        RepoMem(u, Package(n, sel[n]));
      }
    }

    // root inclusion and version uniqueness.
    SelMem(sel, rootPkg);
    assert RootInclusion(rootPkg, r);                // rootName in sel
    forall p, q | p in r && q in r && p.name == q.name ensures p.version == q.version {
      SelMem(sel, p); SelMem(sel, q);
    }
    assert VersionUniqueness(r);

    ClosureIffEdgeCond(u, sel);
  }

  // Composed with Theorem 3.2.7: graph resolution is an ordinary CORE
  // resolution over the reduced problem — the existing resolver applies, no new
  // machinery. The novelty is deriving the per-edge formula from provenance.
  lemma GraphReducesToCore(u: Universe, rootName: Name, sel: map<Name, Version>)
    requires WfGraph(u) && rootName in sel
    ensures ValidGraphResolution(u, rootName, sel)
        <==> ValidResolution(Repo(u), ReduceVf(Repo(u), ToVfDeps(u)),
                             Package(rootName, sel[rootName]), SelToSet(sel))
  {
    GraphReducesToVf(u, rootName, sel);
    VfReductionCorrect(Repo(u), ToVfDeps(u), Package(rootName, sel[rootName]), SelToSet(sel));
  }
}
