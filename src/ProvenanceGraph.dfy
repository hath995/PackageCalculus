// ProvenanceGraph.dfy — multi-library resolution over per-object provenance.
// NOT from the paper. Lifts the single-library import-set model of
// Provenance.dfy to a whole dependency graph: each released version of each
// library carries out-edges to the libraries it imports, anchored at the
// version it was authored against. A resolution selects one version per library
// such that every out-edge of every selected version is satisfied IN-FORM by
// the selected version of its target. Because selecting a library version
// activates that version's own out-edges, a pick propagates transitively.
//
// Each edge's satisfying set is an interval (ProvenanceGraphLemmas.EdgeWindowConvex)
// — a §3.2 version formula whose upper bound is the next breaking change of an
// imported object, which (unlike the latest-anchored window) may lie strictly
// below the latest version. So graph resolution is the core calculus with
// provenance-derived interval dependencies.

include "Provenance.dfy"

module ProvenanceGraph {
  import opened Core
  import opened Versions
  import opened Provenance

  // Version v of a library satisfies an edge (anchor a, imports s): every
  // imported object is present at v in the same form (era) it had at a. Total
  // given WfHistory — a malformed edge (anchor out of range, or an import absent
  // at the anchor) is simply never satisfied.
  predicate EdgeSatH(h: History, a: Version, s: set<Obj>, v: Version)
    requires WfHistory(h)
  {
    ValidVersion(h, a) && ValidVersion(h, v)
    && (forall o | o in s :: Present(h, o, a))
    && (forall o | o in s :: Present(h, o, v) && LastBreak(h, o, v) == LastBreak(h, o, a))
  }

  // An out-edge: import `imports` from library `target`, authored against
  // version `anchor` of it.
  datatype Edge = Edge(target: Name, anchor: Version, imports: set<Obj>)

  // The repository: each library's history, and the out-edges of each released
  // (library, version).
  datatype Universe = Universe(hist: map<Name, History>, edges: map<(Name, Version), set<Edge>>)

  predicate WfUniverse(u: Universe) {
    forall n | n in u.hist :: WfHistory(u.hist[n])
  }

  // A selection assigns one version per library in the resolution. Valid when it
  // contains the root, every chosen version exists, and every out-edge of every
  // selected (library, version) is satisfied in-form by the selected version of
  // its target. Single-version-per-library is automatic: a selection is a map.
  // Every out-edge of every selected (library, version) is satisfied in-form by
  // the selected version of its target.
  predicate EdgeCond(u: Universe, sel: map<Name, Version>)
    requires WfUniverse(u)
  {
    forall n | n in sel && (n, sel[n]) in u.edges ::
      forall e | e in u.edges[(n, sel[n])] ::
        e.target in sel
        && e.target in u.hist
        && EdgeSatH(u.hist[e.target], e.anchor, e.imports, sel[e.target])
  }

  predicate ValidGraphResolution(u: Universe, root: Name, sel: map<Name, Version>)
    requires WfUniverse(u)
  {
    root in sel
    && (forall n | n in sel :: n in u.hist && ValidVersion(u.hist[n], sel[n]))
    && EdgeCond(u, sel)
  }

  // ---- each edge as a §3.2 version formula --------------------------------
  //
  // A well-formed edge: its anchor is a real version of the target and every
  // import exists there. Then its satisfying set is a non-empty interval
  // (ProvenanceGraphLemmas.EdgeWindowConvex / EdgeVersionsInterval), so it is
  // exactly a §3.2 version formula `>= join && <= hi`. join is the latest
  // last_changed among the imports at the anchor; hi is the next version at
  // which an import breaks or disappears — which may sit strictly below the
  // latest version, the cross-anchor reach the latest-anchored window lacked.

  predicate WfEdge(h: History, a: Version, s: set<Obj>) {
    WfHistory(h) && ValidVersion(h, a) && forall o | o in s :: Present(h, o, a)
  }

  // The versions of the target that satisfy the edge.
  function EdgeVersions(h: History, a: Version, s: set<Obj>): set<Version>
    requires WfHistory(h)
  {
    set v: Version | v < |h.releases| && EdgeSatH(h, a, s, v)
  }

  // The lower bound: the join (max last_changed of the imports at the anchor),
  // or 0 when there are no imports.
  function EdgeJoin(h: History, a: Version, s: set<Obj>): Version
    requires WfEdge(h, a, s)
  {
    if s == {} then 0
    else
      var imgs := set o | o in s :: LastBreak(h, o, a);
      assert imgs != {} by { var o :| o in s; assert LastBreak(h, o, a) in imgs; }
      SetMax(imgs)
  }

  // The upper bound: the greatest satisfying version (well-defined because the
  // anchor itself satisfies the edge, so the set is non-empty).
  function EdgeHi(h: History, a: Version, s: set<Obj>): Version
    requires WfEdge(h, a, s)
    ensures EdgeHi(h, a, s) in EdgeVersions(h, a, s)
  {
    assert EdgeSatH(h, a, s, a);
    assert a in EdgeVersions(h, a, s);
    SetMax(EdgeVersions(h, a, s))
  }

  // The edge as a §3.2 version formula: `>= join && <= hi`.
  function EdgeFormula(h: History, a: Version, s: set<Obj>): VFormula
    requires WfEdge(h, a, s)
  {
    VAnd(VCmp(Ge, EdgeJoin(h, a, s)), VCmp(Le, EdgeHi(h, a, s)))
  }

  // ---- reduction to the Version Formula Calculus (§3.2) -------------------
  //
  // A graph whose every edge is well-formed reduces to an ordinary §3.2 version
  // formula problem: the repository is every (library, version), and each edge
  // becomes a VfDep on its target carrying the edge formula. A selection maps to
  // a package set, and (ProvenanceGraphLemmas.GraphReducesToVf) graph resolution
  // is exactly ValidVfResolution over the reduction — hence, via Theorem 3.2.7,
  // an ordinary core resolution. No new resolver: the existing one applies.

  predicate WfGraph(u: Universe) {
    WfUniverse(u)
    && forall k | k in u.edges :: forall e | e in u.edges[k] ::
         e.target in u.hist && WfEdge(u.hist[e.target], e.anchor, e.imports)
  }

  // The versions 0 .. k-1, as a set (membership: ProvenanceGraphLemmas.VRangeMem).
  function VRange(k: nat): set<Version> {
    if k == 0 then {} else VRange(k - 1) + {k - 1}
  }

  // The repository: every released (library, version) as a package.
  function Repo(u: Universe): set<Package>
    requires WfUniverse(u)
  {
    set n, v | n in u.hist && v in VRange(|u.hist[n].releases|) :: Package(n, v)
  }

  // Each out-edge of each released version becomes a version-formula dependency
  // of that package on the edge's target, carrying the edge formula.
  function ToVfDeps(u: Universe): VfDepRel
    requires WfGraph(u)
  {
    set k, e | k in u.edges && e in u.edges[k]
      :: (Package(k.0, k.1), VfDep(e.target, EdgeFormula(u.hist[e.target], e.anchor, e.imports)))
  }

  // A selection as a package set (one version per library).
  function SelToSet(sel: map<Name, Version>): set<Package> {
    set n | n in sel :: Package(n, sel[n])
  }
}
