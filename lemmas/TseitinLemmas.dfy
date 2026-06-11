// TseitinLemmas.dfy — Proofs for the package formula reduction (§4.5).
//
//   Theorem 4.5.5 (Soundness):   a core resolution of the Tseitin-reduced
//     instance, restricted to the original repository, satisfies every
//     selected package's formula. The invariant: if a formula's encoded
//     targets are all satisfied (positively or negatively), the formula
//     holds (or fails) in the restriction.
//   Theorem 4.5.6 (Completeness): a formula-calculus resolution extended
//     with the witness sets W(ψ) (and the conflict packages pushed to
//     version 0 by selected packages) is a valid core resolution.
//
// Both proofs are structural inductions over formulae, with De Morgan's
// laws realised by the polarity flag of EncTargets/EncAuxEdges/PfWitness.

include "../src/PackageFormulae.dfy"

module TseitinLemmas {
  import opened Core
  import opened PackageFormulae

  // ---------------------------------------------------------------------
  // Structure of the encoding.
  // ---------------------------------------------------------------------

  // Synthetic packages carry OrName or NegName names.
  lemma AuxRepoShape(f: PFormula, neg: bool, q: Package)
    requires q in EncAuxRepo(f, neg)
    ensures q.name.OrName? || q.name.NegName?
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
    case PAnd(a, b) =>
      if !neg {
        if q in EncAuxRepo(a, false) { AuxRepoShape(a, false, q); }
        else { AuxRepoShape(b, false, q); }
      } else {
        var orn := OrName(PNot(a), PNot(b));
        if q != Package(orn, 0) && q != Package(orn, 1) {
          if q in EncAuxRepo(a, true) { AuxRepoShape(a, true, q); }
          else { AuxRepoShape(b, true, q); }
        }
      }
    case POr(a, b) =>
      if !neg {
        var orn := OrName(a, b);
        if q != Package(orn, 0) && q != Package(orn, 1) {
          if q in EncAuxRepo(a, false) { AuxRepoShape(a, false, q); }
          else { AuxRepoShape(b, false, q); }
        }
      } else {
        if q in EncAuxRepo(a, true) { AuxRepoShape(a, true, q); }
        else { AuxRepoShape(b, true, q); }
      }
    case PNot(g) => AuxRepoShape(g, !neg, q);
  }

  // Both versions of a conflict package exist in the synthetic repository.
  lemma AuxRepoNegBoth(f: PFormula, neg: bool, q: Package)
    requires q in EncAuxRepo(f, neg) && q.name.NegName?
    ensures Package(q.name, 0) in EncAuxRepo(f, neg)
    ensures Package(q.name, 1) in EncAuxRepo(f, neg)
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
    case PAnd(a, b) =>
      if !neg {
        if q in EncAuxRepo(a, false) { AuxRepoNegBoth(a, false, q); }
        else { AuxRepoNegBoth(b, false, q); }
      } else {
        if q in EncAuxRepo(a, true) { AuxRepoNegBoth(a, true, q); }
        else { AuxRepoNegBoth(b, true, q); }
      }
    case POr(a, b) =>
      if !neg {
        if q in EncAuxRepo(a, false) { AuxRepoNegBoth(a, false, q); }
        else { AuxRepoNegBoth(b, false, q); }
      } else {
        if q in EncAuxRepo(a, true) { AuxRepoNegBoth(a, true, q); }
        else { AuxRepoNegBoth(b, true, q); }
      }
    case PNot(g) => AuxRepoNegBoth(g, !neg, q);
  }

  // A disjunction package present in the synthetic repository has, in the
  // encoding, an edge to each target of the disjunct its version selects.
  lemma AuxOrEdges(f: PFormula, neg: bool, x: PFormula, y: PFormula, bnd: Version, t: Dep)
    requires Package(OrName(x, y), bnd) in EncAuxRepo(f, neg)
    requires bnd == 0 || bnd == 1
    requires t in EncTargets(if bnd == 0 then x else y, false)
    ensures (Package(OrName(x, y), bnd), t) in EncAuxEdges(f, neg)
    decreases FSize(f)
  {
    var q := Package(OrName(x, y), bnd);
    match f
    case PAtom(n, vs) =>
    case PAnd(a, b) =>
      if !neg {
        if q in EncAuxRepo(a, false) { AuxOrEdges(a, false, x, y, bnd, t); }
        else { AuxOrEdges(b, false, x, y, bnd, t); }
      } else {
        var orn := OrName(PNot(a), PNot(b));
        if q == Package(orn, 0) || q == Package(orn, 1) {
          assert x == PNot(a) && y == PNot(b);
          assert EncTargets(x, false) == EncTargets(a, true);
          assert EncTargets(y, false) == EncTargets(b, true);
        } else {
          if q in EncAuxRepo(a, true) { AuxOrEdges(a, true, x, y, bnd, t); }
          else { AuxOrEdges(b, true, x, y, bnd, t); }
        }
      }
    case POr(a, b) =>
      if !neg {
        var orn := OrName(a, b);
        if q == Package(orn, 0) || q == Package(orn, 1) {
          assert x == a && y == b;
        } else {
          if q in EncAuxRepo(a, false) { AuxOrEdges(a, false, x, y, bnd, t); }
          else { AuxOrEdges(b, false, x, y, bnd, t); }
        }
      } else {
        if q in EncAuxRepo(a, true) { AuxOrEdges(a, true, x, y, bnd, t); }
        else { AuxOrEdges(b, true, x, y, bnd, t); }
      }
    case PNot(g) => AuxOrEdges(g, !neg, x, y, bnd, t);
  }

  // A conflict package present in the synthetic repository has its push
  // edges from every conflicting package.
  lemma AuxNegEdges(f: PFormula, neg: bool, q: Package, u: Version)
    requires q in EncAuxRepo(f, neg) && q.name.NegName?
    requires u in q.name.nscope
    ensures (Package(q.name.nbase, u), Dep(q.name, {0 as Version})) in EncAuxEdges(f, neg)
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
    case PAnd(a, b) =>
      if !neg {
        if q in EncAuxRepo(a, false) { AuxNegEdges(a, false, q, u); }
        else { AuxNegEdges(b, false, q, u); }
      } else {
        if q in EncAuxRepo(a, true) { AuxNegEdges(a, true, q, u); }
        else { AuxNegEdges(b, true, q, u); }
      }
    case POr(a, b) =>
      if !neg {
        if q in EncAuxRepo(a, false) { AuxNegEdges(a, false, q, u); }
        else { AuxNegEdges(b, false, q, u); }
      } else {
        if q in EncAuxRepo(a, true) { AuxNegEdges(a, true, q, u); }
        else { AuxNegEdges(b, true, q, u); }
      }
    case PNot(g) => AuxNegEdges(g, !neg, q, u);
  }

  // Every encoded edge is either a disjunction edge or a push edge of a
  // negated atom (with the shapes the closure proofs rely on).
  lemma AuxEdgeShape(f: PFormula, neg: bool, ed: (Package, Dep))
    requires PlainPfFormula(f)
    requires ed in EncAuxEdges(f, neg)
    ensures (ed.0.name.OrName? && (ed.0.version == 0 || ed.0.version == 1)
             && ed.1 in EncTargets(if ed.0.version == 0 then ed.0.name.oleft else ed.0.name.oright, false))
         || (!ed.0.name.OrName? && !ed.0.name.NegName?
             && ed.1.name.NegName? && ed.1 == Dep(ed.1.name, {0 as Version})
             && ed.0.name == ed.1.name.nbase && ed.0.version in ed.1.name.nscope
             && Package(ed.1.name, 0) in EncAuxRepo(f, neg))
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
    case PAnd(a, b) =>
      if !neg {
        if ed in EncAuxEdges(a, false) { AuxEdgeShape(a, false, ed); }
        else { AuxEdgeShape(b, false, ed); }
      } else {
        var orn := OrName(PNot(a), PNot(b));
        if ed in (set t | t in EncTargets(a, true) :: (Package(orn, 0), t)) {
          assert EncTargets(orn.oleft, false) == EncTargets(a, true);
        } else if ed in (set t | t in EncTargets(b, true) :: (Package(orn, 1), t)) {
          assert EncTargets(orn.oright, false) == EncTargets(b, true);
        } else if ed in EncAuxEdges(a, true) {
          AuxEdgeShape(a, true, ed);
        } else {
          AuxEdgeShape(b, true, ed);
        }
      }
    case POr(a, b) =>
      if !neg {
        var orn := OrName(a, b);
        if ed in (set t | t in EncTargets(a, false) :: (Package(orn, 0), t)) {
        } else if ed in (set t | t in EncTargets(b, false) :: (Package(orn, 1), t)) {
        } else if ed in EncAuxEdges(a, false) {
          AuxEdgeShape(a, false, ed);
        } else {
          AuxEdgeShape(b, false, ed);
        }
      } else {
        if ed in EncAuxEdges(a, true) { AuxEdgeShape(a, true, ed); }
        else { AuxEdgeShape(b, true, ed); }
      }
    case PNot(g) => AuxEdgeShape(g, !neg, ed);
  }

  // ---------------------------------------------------------------------
  // Theorem 4.5.5 (Soundness).
  // ---------------------------------------------------------------------

  // Packages of the original repository are exactly the plain ones.
  lemma ReducedPlainInRepo(repo: set<Package>, pfdeps: PfDepRel, p: Package)
    requires p in PfReduceRepo(repo, pfdeps)
    requires !p.name.OrName? && !p.name.NegName?
    ensures p in repo
  {
    if p !in repo {
      var e, q :| e in pfdeps && q in EncAuxRepo(e.1, false) && p == q;
      AuxRepoShape(e.1, false, q);
    }
  }

  // The soundness invariant: satisfied targets make the formula true (at
  // positive polarity) or false (at negative polarity) in the restriction.
  @IsolateAssertions
  lemma SoundInv(repo: set<Package>, pfdeps: PfDepRel, r: set<Package>,
                 f: PFormula, neg: bool)
    requires PlainPfInstance(repo, pfdeps)
    requires PlainPfFormula(f)
    requires r <= PfReduceRepo(repo, pfdeps)
    requires DepClosure(PfReduceDeps(pfdeps), r)
    requires VersionUniqueness(r)
    requires EncAuxEdges(f, neg) <= PfReduceDeps(pfdeps)
    requires TargetsSatisfied(r, EncTargets(f, neg))
    ensures !neg ==> PfSat(r * repo, f)
    ensures neg ==> !PfSat(r * repo, f)
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
      if !neg {
        var t := Dep(n, vs);
        assert t in EncTargets(f, false);
        var v :| v in vs && Package(n, v) in r;
        ReducedPlainInRepo(repo, pfdeps, Package(n, v));
        assert Package(n, v) in r * repo;
      } else {
        var t := Dep(NegName(n, vs), {1 as Version});
        assert t in EncTargets(f, true);
        var w :| w in t.versions && Package(t.name, w) in r;
        assert Package(NegName(n, vs), 1) in r;
        if PfSat(r * repo, f) {
          var u :| u in vs && Package(n, u) in r * repo;
          var push := (Package(n, u), Dep(NegName(n, vs), {0 as Version}));
          assert push in EncAuxEdges(f, true);
          var w0 :| w0 in push.1.versions && Package(push.1.name, w0) in r;
          assert Package(NegName(n, vs), 0) in r;
          assert false;  // version uniqueness on the conflict package
        }
      }
    case PAnd(a, b) =>
      if !neg {
        SoundInv(repo, pfdeps, r, a, false);
        SoundInv(repo, pfdeps, r, b, false);
      } else {
        var orn := OrName(PNot(a), PNot(b));
        var t := Dep(orn, {0 as Version, 1 as Version});
        assert t in EncTargets(f, true);
        var bnd :| bnd in t.versions && Package(orn, bnd) in r;
        if bnd == 0 {
          forall tt | tt in EncTargets(a, true)
            ensures exists v :: v in tt.versions && Package(tt.name, v) in r
          {
            assert (Package(orn, 0), tt) in EncAuxEdges(f, true);
          }
          SoundInv(repo, pfdeps, r, a, true);
        } else {
          forall tt | tt in EncTargets(b, true)
            ensures exists v :: v in tt.versions && Package(tt.name, v) in r
          {
            assert (Package(orn, 1), tt) in EncAuxEdges(f, true);
          }
          SoundInv(repo, pfdeps, r, b, true);
        }
      }
    case POr(a, b) =>
      if !neg {
        var orn := OrName(a, b);
        var t := Dep(orn, {0 as Version, 1 as Version});
        assert t in EncTargets(f, false);
        var bnd :| bnd in t.versions && Package(orn, bnd) in r;
        if bnd == 0 {
          forall tt | tt in EncTargets(a, false)
            ensures exists v :: v in tt.versions && Package(tt.name, v) in r
          {
            assert (Package(orn, 0), tt) in EncAuxEdges(f, false);
          }
          SoundInv(repo, pfdeps, r, a, false);
        } else {
          forall tt | tt in EncTargets(b, false)
            ensures exists v :: v in tt.versions && Package(tt.name, v) in r
          {
            assert (Package(orn, 1), tt) in EncAuxEdges(f, false);
          }
          SoundInv(repo, pfdeps, r, b, false);
        }
      } else {
        SoundInv(repo, pfdeps, r, a, true);
        SoundInv(repo, pfdeps, r, b, true);
      }
    case PNot(g) =>
      SoundInv(repo, pfdeps, r, g, !neg);
  }

  // Theorem 4.5.5.
  lemma PfReductionSound(repo: set<Package>, pfdeps: PfDepRel, root: Package, r: set<Package>)
    requires PlainPfInstance(repo, pfdeps)
    requires root in repo
    requires ValidResolution(PfReduceRepo(repo, pfdeps), PfReduceDeps(pfdeps), root, r)
    ensures ValidPfResolution(repo, pfdeps, root, r * repo)
  {
    forall e | e in pfdeps && e.0 in r * repo
      ensures PfSat(r * repo, e.1)
    {
      forall t | t in EncTargets(e.1, false)
        ensures exists v :: v in t.versions && Package(t.name, v) in r
      {
        assert (e.0, t) in PfReduceDeps(pfdeps);
      }
      assert EncAuxEdges(e.1, false) <= PfReduceDeps(pfdeps);
      SoundInv(repo, pfdeps, r, e.1, false);
    }
  }

  // ---------------------------------------------------------------------
  // Theorem 4.5.6 (Completeness).
  // ---------------------------------------------------------------------

  // The witness set draws only on the formula's synthetic packages.
  lemma WitnessSubRepo(r: set<Package>, f: PFormula, neg: bool)
    ensures PfWitness(r, f, neg) <= EncAuxRepo(f, neg)
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
    case PAnd(a, b) =>
      if !neg {
        WitnessSubRepo(r, a, false);
        WitnessSubRepo(r, b, false);
      } else {
        WitnessSubRepo(r, a, true);
        WitnessSubRepo(r, b, true);
      }
    case POr(a, b) =>
      if !neg {
        WitnessSubRepo(r, a, false);
        WitnessSubRepo(r, b, false);
      } else {
        WitnessSubRepo(r, a, true);
        WitnessSubRepo(r, b, true);
      }
    case PNot(g) => WitnessSubRepo(r, g, !neg);
  }

  // Disjunction packages in the witness always carry the canonical choice:
  // version 0 exactly when the left disjunct holds.
  lemma WitnessOrVersion(r: set<Package>, f: PFormula, neg: bool, q: Package)
    requires q in PfWitness(r, f, neg) && q.name.OrName?
    ensures q.version == (if PfSat(r, q.name.oleft) then 0 else 1)
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
    case PAnd(a, b) =>
      if !neg {
        if q in PfWitness(r, a, false) { WitnessOrVersion(r, a, false, q); }
        else { WitnessOrVersion(r, b, false, q); }
      } else {
        var orn := OrName(PNot(a), PNot(b));
        if q.name == orn && (q == Package(orn, 0) || q == Package(orn, 1)) &&
           (q !in PfWitness(r, a, true) && q !in PfWitness(r, b, true)) {
          assert q.name.oleft == PNot(a);
        } else if !PfSat(r, a) && q in PfWitness(r, a, true) {
          WitnessOrVersion(r, a, true, q);
        } else if PfSat(r, a) && q in PfWitness(r, b, true) {
          WitnessOrVersion(r, b, true, q);
        } else {
          assert q.name == orn;
          assert q.name.oleft == PNot(a);
        }
      }
    case POr(a, b) =>
      if !neg {
        var orn := OrName(a, b);
        if PfSat(r, a) && q in PfWitness(r, a, false) {
          WitnessOrVersion(r, a, false, q);
        } else if !PfSat(r, a) && q in PfWitness(r, b, false) {
          WitnessOrVersion(r, b, false, q);
        } else {
          assert q.name == orn;
          assert q.name.oleft == a;
        }
      } else {
        if q in PfWitness(r, a, true) { WitnessOrVersion(r, a, true, q); }
        else { WitnessOrVersion(r, b, true, q); }
      }
    case PNot(g) => WitnessOrVersion(r, g, !neg, q);
  }

  // Conflict packages in the witness sit at version 1, and only for atoms
  // the resolution falsifies.
  lemma WitnessNegShape(r: set<Package>, f: PFormula, neg: bool, q: Package)
    requires if !neg then PfSat(r, f) else !PfSat(r, f)
    requires q in PfWitness(r, f, neg) && q.name.NegName?
    ensures q.version == 1
    ensures !PfSat(r, PAtom(q.name.nbase, q.name.nscope))
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
      assert q == Package(NegName(n, vs), 1);
    case PAnd(a, b) =>
      if !neg {
        if q in PfWitness(r, a, false) { WitnessNegShape(r, a, false, q); }
        else { WitnessNegShape(r, b, false, q); }
      } else {
        if !PfSat(r, a) {
          assert q in PfWitness(r, a, true);
          WitnessNegShape(r, a, true, q);
        } else {
          assert !PfSat(r, b);
          assert q in PfWitness(r, b, true);
          WitnessNegShape(r, b, true, q);
        }
      }
    case POr(a, b) =>
      if !neg {
        if PfSat(r, a) {
          assert q in PfWitness(r, a, false);
          WitnessNegShape(r, a, false, q);
        } else {
          assert PfSat(r, b);
          assert q in PfWitness(r, b, false);
          WitnessNegShape(r, b, false, q);
        }
      } else {
        if q in PfWitness(r, a, true) { WitnessNegShape(r, a, true, q); }
        else { WitnessNegShape(r, b, true, q); }
      }
    case PNot(g) => WitnessNegShape(r, g, !neg, q);
  }

  // A disjunction package in the witness selects a satisfied disjunct
  // whose own witness is included.
  lemma WitnessOrChar(r: set<Package>, f: PFormula, neg: bool,
                      x: PFormula, y: PFormula, bnd: Version)
    requires if !neg then PfSat(r, f) else !PfSat(r, f)
    requires Package(OrName(x, y), bnd) in PfWitness(r, f, neg)
    ensures bnd == 0 || bnd == 1
    ensures PfSat(r, if bnd == 0 then x else y)
    ensures PfWitness(r, if bnd == 0 then x else y, false) <= PfWitness(r, f, neg)
    decreases FSize(f)
  {
    var q := Package(OrName(x, y), bnd);
    match f
    case PAtom(n, vs) =>
    case PAnd(a, b) =>
      if !neg {
        if q in PfWitness(r, a, false) { WitnessOrChar(r, a, false, x, y, bnd); }
        else { WitnessOrChar(r, b, false, x, y, bnd); }
      } else {
        var orn := OrName(PNot(a), PNot(b));
        if !PfSat(r, a) {
          if q == Package(orn, 0) {
            assert x == PNot(a) && bnd == 0;
            assert PfWitness(r, x, false) == PfWitness(r, a, true);
          } else {
            WitnessOrChar(r, a, true, x, y, bnd);
          }
        } else {
          assert !PfSat(r, b);
          if q == Package(orn, 1) {
            assert y == PNot(b) && bnd == 1;
            assert PfWitness(r, y, false) == PfWitness(r, b, true);
          } else {
            WitnessOrChar(r, b, true, x, y, bnd);
          }
        }
      }
    case POr(a, b) =>
      if !neg {
        var orn := OrName(a, b);
        if PfSat(r, a) {
          if q == Package(orn, 0) {
            assert x == a && bnd == 0;
          } else {
            WitnessOrChar(r, a, false, x, y, bnd);
          }
        } else {
          assert PfSat(r, b);
          if q == Package(orn, 1) {
            assert y == b && bnd == 1;
          } else {
            WitnessOrChar(r, b, false, x, y, bnd);
          }
        }
      } else {
        if q in PfWitness(r, a, true) { WitnessOrChar(r, a, true, x, y, bnd); }
        else { WitnessOrChar(r, b, true, x, y, bnd); }
      }
    case PNot(g) => WitnessOrChar(r, g, !neg, x, y, bnd);
  }

  // The completeness invariant: the witness packages make the encoded
  // targets satisfied.
  lemma CompInv(r: set<Package>, rhat: set<Package>, f: PFormula, neg: bool)
    requires if !neg then PfSat(r, f) else !PfSat(r, f)
    requires r <= rhat
    requires PfWitness(r, f, neg) <= rhat
    ensures TargetsSatisfied(rhat, EncTargets(f, neg))
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
      if !neg {
        var v :| v in vs && Package(n, v) in r;
        assert Package(n, v) in rhat;
      } else {
        assert Package(NegName(n, vs), 1) in rhat;
      }
    case PAnd(a, b) =>
      if !neg {
        CompInv(r, rhat, a, false);
        CompInv(r, rhat, b, false);
      } else {
        var orn := OrName(PNot(a), PNot(b));
        if !PfSat(r, a) {
          assert Package(orn, 0) in rhat;
        } else {
          assert Package(orn, 1) in rhat;
        }
      }
    case POr(a, b) =>
      if !neg {
        var orn := OrName(a, b);
        if PfSat(r, a) {
          assert Package(orn, 0) in rhat;
        } else {
          assert Package(orn, 1) in rhat;
        }
      } else {
        CompInv(r, rhat, a, true);
        CompInv(r, rhat, b, true);
      }
    case PNot(g) =>
      CompInv(r, rhat, g, !neg);
  }

  // Decomposing the built resolution: original packages, witness
  // disjunction/conflict packages, or pushed conflict packages.
  lemma BuildDecompose(repo: set<Package>, pfdeps: PfDepRel, r: set<Package>, q: Package)
    requires r <= repo
    requires forall p | p in repo :: !p.name.OrName? && !p.name.NegName?
    requires q in PfBuildCore(r, pfdeps)
    ensures q.name.OrName? || q.name.NegName? || q in r
    ensures q.name.OrName? ==> q in PfWitnessPart(r, pfdeps)
    ensures q.name.NegName? ==> q in PfWitnessPart(r, pfdeps) || q in PfPushNegs(r, pfdeps)
  {
    if q in PfWitnessPart(r, pfdeps) {
      var e, q' :| e in pfdeps && e.0 in r && q' in PfWitness(r, e.1, false) && q == q';
      WitnessSubRepo(r, e.1, false);
      AuxRepoShape(e.1, false, q);
    } else if q in PfPushNegs(r, pfdeps) {
      var e, q' :| e in pfdeps && q' in EncAuxRepo(e.1, false) && q'.name.NegName?
            && (exists u :: u in q'.name.nscope && Package(q'.name.nbase, u) in r)
            && q == Package(q'.name, 0);
    }
  }

  // Version uniqueness of the built resolution.
  @IsolateAssertions
  lemma BuildUnique(repo: set<Package>, pfdeps: PfDepRel, r: set<Package>)
    requires PlainPfInstance(repo, pfdeps)
    requires r <= repo
    requires VersionUniqueness(r)
    requires PfClosure(pfdeps, r)
    ensures VersionUniqueness(PfBuildCore(r, pfdeps))
  {
    var rhat := PfBuildCore(r, pfdeps);
    forall p, q | p in rhat && q in rhat && p.name == q.name
      ensures p.version == q.version
    {
      BuildDecompose(repo, pfdeps, r, p);
      BuildDecompose(repo, pfdeps, r, q);
      if p.name.OrName? {
        OrMemberVersion(repo, pfdeps, r, p);
        OrMemberVersion(repo, pfdeps, r, q);
      } else if p.name.NegName? {
        NegMemberVersion(repo, pfdeps, r, p);
        NegMemberVersion(repo, pfdeps, r, q);
      } else {
        // both in r
      }
    }
  }

  // Any disjunction package in the built resolution carries the canonical
  // choice version.
  lemma OrMemberVersion(repo: set<Package>, pfdeps: PfDepRel, r: set<Package>, p: Package)
    requires PlainPfInstance(repo, pfdeps)
    requires r <= repo
    requires PfClosure(pfdeps, r)
    requires p in PfWitnessPart(r, pfdeps) && p.name.OrName?
    ensures p.version == (if PfSat(r, p.name.oleft) then 0 else 1)
  {
    var e, q :| e in pfdeps && e.0 in r && q in PfWitness(r, e.1, false) && p == q;
    assert PfSat(r, e.1);  // closure
    WitnessOrVersion(r, e.1, false, p);
  }

  // Any conflict package in the built resolution carries the version
  // dictated by the truth of its atom.
  lemma NegMemberVersion(repo: set<Package>, pfdeps: PfDepRel, r: set<Package>, p: Package)
    requires PlainPfInstance(repo, pfdeps)
    requires r <= repo
    requires PfClosure(pfdeps, r)
    requires p.name.NegName?
    requires p in PfWitnessPart(r, pfdeps) || p in PfPushNegs(r, pfdeps)
    ensures p.version == (if PfSat(r, PAtom(p.name.nbase, p.name.nscope)) then 0 else 1)
  {
    if p in PfWitnessPart(r, pfdeps) {
      var e, q :| e in pfdeps && e.0 in r && q in PfWitness(r, e.1, false) && p == q;
      assert PfSat(r, e.1);  // closure
      WitnessNegShape(r, e.1, false, p);
    } else {
      var e, q :| e in pfdeps && q in EncAuxRepo(e.1, false) && q.name.NegName?
            && (exists u :: u in q.name.nscope && Package(q.name.nbase, u) in r)
            && p == Package(q.name, 0);
      var u :| u in q.name.nscope && Package(q.name.nbase, u) in r;
      assert PfSat(r, PAtom(p.name.nbase, p.name.nscope));
    }
  }

  // Dependency closure of the built resolution.
  @IsolateAssertions
  lemma BuildClosure(repo: set<Package>, pfdeps: PfDepRel, r: set<Package>)
    requires PlainPfInstance(repo, pfdeps)
    requires r <= repo
    requires VersionUniqueness(r)
    requires PfClosure(pfdeps, r)
    ensures DepClosure(PfReduceDeps(pfdeps), PfBuildCore(r, pfdeps))
  {
    var rhat := PfBuildCore(r, pfdeps);
    forall ed | ed in PfReduceDeps(pfdeps) && ed.0 in rhat
      ensures exists v :: v in ed.1.versions && Package(ed.1.name, v) in rhat
    {
      if ed in (set e, t | e in pfdeps && t in EncTargets(e.1, false) :: (e.0, t)) {
        // Depender → target edge.
        var e, t :| e in pfdeps && t in EncTargets(e.1, false) && ed == (e.0, t);
        BuildDecompose(repo, pfdeps, r, ed.0);
        assert ed.0 in r;  // dependers are plain repo packages
        assert PfSat(r, e.1);
        WitnessInRhat(repo, pfdeps, r, e);
        CompInv(r, rhat, e.1, false);
      } else {
        // Auxiliary edge of some formula.
        var e, aux :| e in pfdeps && aux in EncAuxEdges(e.1, false) && ed == aux;
        AuxEdgeShape(e.1, false, ed);
        if ed.0.name.OrName? {
          BuildDecompose(repo, pfdeps, r, ed.0);
          var e2, q :| e2 in pfdeps && e2.0 in r && q in PfWitness(r, e2.1, false) && ed.0 == q;
          assert PfSat(r, e2.1);
          WitnessOrChar(r, e2.1, false, ed.0.name.oleft, ed.0.name.oright, ed.0.version);
          var side := if ed.0.version == 0 then ed.0.name.oleft else ed.0.name.oright;
          WitnessInRhat(repo, pfdeps, r, e2);
          assert PfWitness(r, side, false) <= rhat;
          CompInv(r, rhat, side, false);
        } else {
          // Push edge: the conflicting package is selected, so the
          // conflict package sits at version 0.
          BuildDecompose(repo, pfdeps, r, ed.0);
          assert ed.0 in r;
          assert Package(ed.1.name, 0) in PfPushNegs(r, pfdeps);
          assert 0 in ed.1.versions && Package(ed.1.name, 0) in rhat;
        }
      }
    }
  }

  // The witness of a selected dependency is inside the built resolution.
  lemma WitnessInRhat(repo: set<Package>, pfdeps: PfDepRel, r: set<Package>, e: (Package, PFormula))
    requires e in pfdeps && e.0 in r
    ensures PfWitness(r, e.1, false) <= PfBuildCore(r, pfdeps)
  {
    forall q | q in PfWitness(r, e.1, false)
      ensures q in PfWitnessPart(r, pfdeps)
    {
    }
  }

  // The built resolution stays in the reduced repository.
  lemma BuildSubset(repo: set<Package>, pfdeps: PfDepRel, r: set<Package>)
    requires r <= repo
    ensures PfBuildCore(r, pfdeps) <= PfReduceRepo(repo, pfdeps)
  {
    forall q | q in PfBuildCore(r, pfdeps)
      ensures q in PfReduceRepo(repo, pfdeps)
    {
      if q in r {
        assert q in repo;
      } else if q in PfWitnessPart(r, pfdeps) {
        var e, q' :| e in pfdeps && e.0 in r && q' in PfWitness(r, e.1, false) && q == q';
        WitnessSubRepo(r, e.1, false);
        assert q in EncAuxRepo(e.1, false);
      } else {
        var e, q' :| e in pfdeps && q' in EncAuxRepo(e.1, false) && q'.name.NegName?
              && (exists u :: u in q'.name.nscope && Package(q'.name.nbase, u) in r)
              && q == Package(q'.name, 0);
        AuxRepoNegBoth(e.1, false, q');
        assert q in EncAuxRepo(e.1, false);
      }
    }
  }

  // Theorem 4.5.6.
  lemma PfReductionComplete(repo: set<Package>, pfdeps: PfDepRel, root: Package, r: set<Package>)
    requires PlainPfInstance(repo, pfdeps)
    requires root in repo
    requires ValidPfResolution(repo, pfdeps, root, r)
    ensures ValidResolution(PfReduceRepo(repo, pfdeps), PfReduceDeps(pfdeps),
                            root, PfBuildCore(r, pfdeps))
  {
    BuildSubset(repo, pfdeps, r);
    BuildUnique(repo, pfdeps, r);
    BuildClosure(repo, pfdeps, r);
    assert root in PfBuildCore(r, pfdeps);
  }
}
