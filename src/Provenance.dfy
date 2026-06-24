// Provenance.dfy — per-object change provenance and import-set compatibility
// windows. NOT from the paper: a finer-grained compatibility model in which a
// library is a single linear version timeline, and a consumer's compatible
// version range is derived from the exact set of objects it imports together
// with per-object breaking-change provenance.
//
// The idea (after a design discussion): each object (function, datatype,
// predicate, …) exported by a library has, at the latest version, a
// `last_changed` version — the start of its current breaking-free form. A
// depender imports a SUBSET of the objects. The maximum last_changed over the
// import set is the minimum library version that supports the depender; the
// range stays compatible forward until one of the imported objects next breaks
// (compatible/minor changes do not bound it). That range is an interval, and
// is exactly the §3.2 version formula `>= lo && <= hi` — so windowed
// resolution is ValidVfResolution and inherits Theorem 3.2.7. The coarse
// compatibility class is the special case where the import set is everything.
//
// Theorems are proved in lemmas/ProvenanceLemmas.dfy.

include "Core.dfy"
include "Versions.dfy"

module Provenance {
  import opened Core
  import opened Versions

  // An object/symbol name exported by a library (e.g. "SeqLib.IndexOf").
  type Obj = string

  // One released version of a library: the objects it exports, and which of
  // those changed INCOMPATIBLY at this version relative to the previous one.
  // A newly-appeared object (a birth, including reappearance after removal)
  // is in `broke`: a consumer could not have depended on it earlier, so it
  // starts a fresh stable era. Compatible (minor) changes are NOT recorded in
  // `broke` — they do not bound compatibility.
  datatype Release = Release(objs: set<Obj>, broke: set<Obj>)

  // A library's recorded history. Index v into `releases` is library version
  // v; the latest released version is |releases| - 1.
  datatype History = History(releases: seq<Release>)

  predicate ValidVersion(h: History, v: Version) {
    0 <= v < |h.releases|
  }

  predicate WfHistory(h: History) {
    |h.releases| > 0
    // What broke at a version is among what it exports.
    && (forall v | 0 <= v < |h.releases| :: h.releases[v].broke <= h.releases[v].objs)
    // Every birth is a break: an object present at v but absent at v-1 (or
    // present at the very first version) is in `broke` at v.
    && (forall v | 0 <= v < |h.releases| ::
          forall o | o in h.releases[v].objs && (v == 0 || o !in h.releases[v - 1].objs)
            :: o in h.releases[v].broke)
  }

  function Latest(h: History): Version
    requires WfHistory(h)
  {
    |h.releases| - 1
  }

  predicate Present(h: History, o: Obj, v: Version)
    requires ValidVersion(h, v)
  {
    o in h.releases[v].objs
  }

  predicate BrokeAt(h: History, o: Obj, v: Version)
    requires ValidVersion(h, v)
  {
    o in h.releases[v].broke
  }

  // An object present but not broken at v was already present (in the same
  // era) at v-1 — the contrapositive of "every birth is a break".
  lemma PresentPrevWhenUnbroken(h: History, o: Obj, v: Version)
    requires WfHistory(h) && ValidVersion(h, v)
    requires Present(h, o, v) && !BrokeAt(h, o, v)
    ensures v > 0 && Present(h, o, v - 1)
  {
    // if v == 0 or absent at v-1, WfHistory forces o in broke at v.
  }

  // last_changed: the start of o's current breaking-free form as of version v —
  // the largest u <= v at which o broke. Well-defined when o is present at v,
  // because o's birth (a break) lies at or before v.
  function LastBreak(h: History, o: Obj, v: Version): Version
    requires WfHistory(h) && ValidVersion(h, v) && Present(h, o, v)
    ensures LastBreak(h, o, v) <= v
    ensures ValidVersion(h, LastBreak(h, o, v))
    ensures BrokeAt(h, o, LastBreak(h, o, v))
    decreases v
  {
    if BrokeAt(h, o, v) then v
    else
      PresentPrevWhenUnbroken(h, o, v);
      LastBreak(h, o, v - 1)
  }

  // Two versions show object o in the SAME compatible form: present at both,
  // with the same stable-era start (equivalently, no breaking change between).
  predicate SameForm(h: History, o: Obj, b: Version, w: Version)
    requires WfHistory(h) && ValidVersion(h, b) && ValidVersion(h, w)
  {
    Present(h, o, b) && Present(h, o, w)
    && LastBreak(h, o, b) == LastBreak(h, o, w)
  }

  // ---- import-set windows -------------------------------------------------

  predicate ImportsPresentAtLatest(h: History, s: set<Obj>)
    requires WfHistory(h)
  {
    forall o | o in s :: Present(h, o, Latest(h))
  }

  // The set of last_changed versions of the imported objects (at latest).
  function ImportBreaks(h: History, s: set<Obj>): set<Version>
    requires WfHistory(h) && ImportsPresentAtLatest(h, s)
  {
    set o | o in s :: LastBreak(h, o, Latest(h))
  }

  // The maximum of a non-empty set of versions (the max is unique, so the
  // let-such-that is deterministic and the function compiles).
  lemma MaxExists(s: set<Version>)
    requires s != {}
    ensures exists m :: m in s && forall w | w in s :: w <= m
    decreases s
  {
    var x :| x in s;
    if s != {x} {
      MaxExists(s - {x});
      var m :| m in s - {x} && forall w | w in s - {x} :: w <= m;
      assert forall w | w in s :: w == x || w in s - {x};
    }
  }

  function SetMax(s: set<Version>): Version
    requires s != {}
    ensures SetMax(s) in s
    ensures forall w | w in s :: w <= SetMax(s)
  {
    MaxExists(s);
    var m :| m in s && forall w | w in s :: w <= m;
    m
  }

  // The minimum library version that supports an import set: the maximum, over
  // imported objects, of each object's last_changed (its stable-era start) at
  // the latest version. Empty import set ⇒ 0 (any version supports it).
  function MinSupport(h: History, s: set<Obj>): Version
    requires WfHistory(h) && ImportsPresentAtLatest(h, s)
    ensures MinSupport(h, s) <= Latest(h)
  {
    var breaks := ImportBreaks(h, s);
    if breaks == {} then 0
    else
      assert forall x | x in breaks :: x <= Latest(h);
      SetMax(breaks)
  }

  // The compatible window for import set s, resolved against the latest
  // version: every released version w at which all imported objects have the
  // same form as at the latest version.
  predicate InWindow(h: History, s: set<Obj>, w: Version)
    requires WfHistory(h) && ValidVersion(h, w) && ImportsPresentAtLatest(h, s)
  {
    forall o | o in s :: SameForm(h, o, Latest(h), w)
  }

  // The window as a §3.2 version formula: `>= MinSupport && <= Latest`. Its
  // Eval over the released-version universe is exactly the window (proved in
  // ProvenanceLemmas.WindowAsFormula), so windowed resolution is ordinary
  // Version-Formula resolution and reduces to the core via Theorem 3.2.7.
  function WindowFormula(h: History, s: set<Obj>): VFormula
    requires WfHistory(h) && ImportsPresentAtLatest(h, s)
  {
    VAnd(VCmp(Ge, MinSupport(h, s)), VCmp(Le, Latest(h)))
  }

  // ---- combining import sets across dependers (the join model) ------------
  //
  // [NOT from the paper.] A single depender's imports give a window resolved
  // against the latest version (above). Here SEVERAL dependers each depend on
  // THIS library, and we ask when one version of it satisfies them all.
  //
  // Generalise an import beyond the latest-anchored window: a depender authored
  // against some anchor version requires each imported object o in the *form*
  // (breaking-free era) it had at that anchor — the era starting at
  // LastBreak(o, anchor). Record that as an era requirement (o, e): "I need o
  // with last_changed exactly e." Collect every depender's requirements into a
  // union U.
  //
  // Two facts turn resolution into a single-point check rather than a search:
  //   * Clause 1 (consistency). If one object is required in two distinct eras
  //     (same o, different e), no version shows o in both — unsatisfiable.
  //   * The JOIN. Otherwise let m be the maximum required era over U. Only a
  //     version >= m can satisfy the highest requirement, and only a version
  //     below each object's next break keeps every object in its required era;
  //     the unique minimal candidate is m itself. So U is satisfiable iff
  //     release m still shows every required object in its required era — and
  //     then m IS the resolution (CombinedSatisfiableIffResolves and
  //     JoinLeResolver in lemmas/ProvenanceLemmas.dfy).
  //
  // This is where genuine cross-depender conflict becomes visible. A lone
  // latest-anchored window never excludes the head, so two windows over one
  // library always overlap at the latest version (LatestAnchoredSatisfiable);
  // the join model, by letting eras come from different anchors, can be
  // unsatisfiable (see tests/ProvenanceTests.dfy).

  // An era requirement: object o is needed with last_changed exactly e.
  type EraReq = (Obj, Version)

  // Clause 1: no object is required in two distinct eras.
  predicate SingleTagged(U: set<EraReq>) {
    forall a, b | a in U && b in U && a.0 == b.0 :: a.1 == b.1
  }

  // Each requirement names a real era: a version at which the object exists and
  // broke (a breaking-free era starts at a break). LastBreak(o, anchor) for an
  // object present at the anchor always yields such an era, so requirement sets
  // derived from real imports are well-formed.
  predicate WfReq(h: History, U: set<EraReq>)
    requires WfHistory(h)
  {
    forall r | r in U ::
      ValidVersion(h, r.1) && Present(h, r.0, r.1) && BrokeAt(h, r.0, r.1)
  }

  // Version v satisfies the whole union: every required object is present at v
  // in exactly its required era.
  predicate ResolvesAt(h: History, U: set<EraReq>, v: Version)
    requires WfHistory(h) && ValidVersion(h, v)
  {
    forall r | r in U :: Present(h, r.0, v) && LastBreak(h, r.0, v) == r.1
  }

  // The required eras present in U.
  function ReqEras(U: set<EraReq>): set<Version> {
    set r | r in U :: r.1
  }

  // The join: the maximum required era — the unique minimal version that can
  // satisfy U (minimality proved in ProvenanceLemmas.JoinLeResolver). A released
  // version whenever U is a non-empty well-formed requirement set.
  function Join(h: History, U: set<EraReq>): Version
    requires WfHistory(h) && WfReq(h, U) && U != {}
    ensures Join(h, U) in ReqEras(U)
    ensures ValidVersion(h, Join(h, U))
    ensures forall r | r in U :: r.1 <= Join(h, U)
  {
    assert ReqEras(U) != {} by { var r :| r in U; assert r.1 in ReqEras(U); }
    var m := SetMax(ReqEras(U));
    assert ValidVersion(h, m) by { assert m in ReqEras(U); var r :| r in U && r.1 == m; }
    assert forall r | r in U :: r.1 <= m by {
      forall r | r in U ensures r.1 <= m { assert r.1 in ReqEras(U); }
    }
    m
  }

  // U is satisfiable iff it is consistent (clause 1) and the join still shows
  // every required object in its required era. The empty union is trivially
  // satisfiable. Equivalent to "some version resolves U", with the join as the
  // witness — ProvenanceLemmas.CombinedSatisfiableIffResolves.
  predicate CombinedSatisfiable(h: History, U: set<EraReq>)
    requires WfHistory(h) && WfReq(h, U)
  {
    SingleTagged(U) && (U == {} || ResolvesAt(h, U, Join(h, U)))
  }

  // ---- deriving the requirement union from a dependency set ---------------
  //
  // A depender on THIS library is an anchor version together with the objects
  // it imports (present at that anchor). Its contribution to the requirement
  // union is each imported object pinned to the era it had at the anchor —
  // AnchoredImport. The union over all dependers is UnionReq, and resolving the
  // library against the whole set is CombinedSatisfiable(h, UnionReq(h, ds)).
  //
  // The lemmas live in ProvenanceLemmas.dfy:
  //   AnchoredImportWfReq / UnionReqWfReq  — these sets are well-formed, so the
  //                                          join machinery applies;
  //   GraphResolves                        — satisfiability of the set ⇔ some
  //                                          version resolves it (join witness);
  //   DependerSatisfiedAtJoin              — at a resolving version every
  //                                          depender sees each import in the
  //                                          SAME form it had at its anchor.

  datatype Depender = Depender(anchor: Version, imports: set<Obj>)

  predicate WfDepender(h: History, d: Depender)
    requires WfHistory(h)
  {
    ValidVersion(h, d.anchor) && forall o | o in d.imports :: Present(h, o, d.anchor)
  }

  predicate WfDependers(h: History, ds: set<Depender>)
    requires WfHistory(h)
  {
    forall d | d in ds :: WfDepender(h, d)
  }

  // One depender's requirements: each import in the era it had at the anchor.
  function AnchoredImport(h: History, d: Depender): set<EraReq>
    requires WfHistory(h) && WfDepender(h, d)
  {
    set o | o in d.imports :: (o, LastBreak(h, o, d.anchor))
  }

  // The requirement union induced by a whole set of dependers on this library.
  function UnionReq(h: History, ds: set<Depender>): set<EraReq>
    requires WfHistory(h) && WfDependers(h, ds)
  {
    set d, r | d in ds && r in AnchoredImport(h, d) :: r
  }
}
