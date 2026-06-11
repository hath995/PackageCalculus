// VariableFormulaeLemmas.dfy — Proofs for §4.6.
//
//   SatTransfer:                 a resolution-and-assignment satisfies a
//     variable formula iff the resolution extended with the assignment's
//     variable packages satisfies the compiled package formula.
//   Theorem 4.6.4 (Soundness):   a core resolution of the variable-reduced
//     instance yields a variable-calculus resolution and assignment — via
//     Theorem 4.5.5 and SatTransfer.
//   Theorem 4.6.5 (Completeness): the converse, via SatTransfer and
//     Theorem 4.5.6.

include "../src/VariableFormulae.dfy"
include "TseitinLemmas.dfy"

module VariableFormulaeLemmas {
  import opened Core
  import opened PackageFormulae
  import opened VariableFormulae
  import TseitinLemmas

  lemma VKeyNameInj(k1: VarKey, k2: VarKey)
    requires VKeyName(k1) == VKeyName(k2)
    ensures k1 == k2
  {
  }

  // Compiled formulae are plain package formulae.
  lemma CompilePlain(f: VForm, owner: Package, univ: VarUniverse)
    requires PlainVForm(f)
    ensures PlainPfFormula(Compile(f, owner, univ))
  {
  }

  // The satisfaction-transfer bridge.
  lemma SatTransfer(r: set<Package>, asg: Assignment, univ: VarUniverse,
                    owner: Package, f: VForm)
    requires forall p | p in r :: !p.name.GlobalVarName? && !p.name.LocalVarName?
    requires AsgInUniverse(asg, univ)
    requires PlainVForm(f)
    ensures VSat(r, asg, owner, f) <==> PfSat(r + AsgPkgs(asg), Compile(f, owner, univ))
  {
    var rr := r + AsgPkgs(asg);
    match f
    case VfAtom(n, vs) =>
      // Variable packages cannot witness a plain atom.
      forall v | v in vs
        ensures Package(n, v) in rr <==> Package(n, v) in r
      {
        if Package(n, v) in rr && Package(n, v) !in r {
          var k :| k in asg && Package(n, v) == Package(VKeyName(k), asg[k]);
        }
      }
    case VfAnd(a, b) =>
      SatTransfer(r, asg, univ, owner, a);
      SatTransfer(r, asg, univ, owner, b);
    case VfOr(a, b) =>
      SatTransfer(r, asg, univ, owner, a);
      SatTransfer(r, asg, univ, owner, b);
    case VfNot(g) =>
      SatTransfer(r, asg, univ, owner, g);
    case VfGlobal(g, op, w) =>
      CmpTransfer(r, asg, univ, GlobalVar(g), op, w);
    case VfLocal(l, op, w) =>
      CmpTransfer(r, asg, univ, LocalVar(owner, l), op, w);
  }

  // The comparison case of the transfer: the compiled atom over the
  // variable package holds iff the variable is assigned a value
  // satisfying the comparison.
  lemma CmpTransfer(r: set<Package>, asg: Assignment, univ: VarUniverse,
                    k: VarKey, op: CmpOp, w: VarValue)
    requires forall p | p in r :: !p.name.GlobalVarName? && !p.name.LocalVarName?
    requires AsgInUniverse(asg, univ)
    ensures (k in asg && CmpHolds(op, asg[k], w))
        <==> PfSat(r + AsgPkgs(asg), PAtom(VKeyName(k), CmpVals(univ, k, op, w)))
  {
    var rr := r + AsgPkgs(asg);
    var vals := CmpVals(univ, k, op, w);
    if k in asg && CmpHolds(op, asg[k], w) {
      assert (k, asg[k]) in univ;
      assert asg[k] in vals;
      assert Package(VKeyName(k), asg[k]) in rr;
    }
    if PfSat(rr, PAtom(VKeyName(k), vals)) {
      var v :| v in vals && Package(VKeyName(k), v) in rr;
      assert Package(VKeyName(k), v) !in r;  // r carries no variable packages
      var k' :| k' in asg && Package(VKeyName(k), v) == Package(VKeyName(k'), asg[k']);
      VKeyNameInj(k, k');
      assert k in asg && asg[k] == v;
      var e :| e in univ && e.0 == k && CmpHolds(op, e.1, w) && e.1 == v;
    }
  }

  // The compiled instance is a plain package formula instance.
  lemma CompiledInstancePlain(repo: set<Package>, vdeps: VFormDepRel, univ: VarUniverse)
    requires PlainVarInstance(repo, vdeps)
    ensures PlainPfInstance(repo + VarPkgsUniverse(univ), CompileDeps(vdeps, univ))
  {
    forall p | p in repo + VarPkgsUniverse(univ)
      ensures !p.name.OrName? && !p.name.NegName?
    {
      if p !in repo {
        var e :| e in univ && p == Package(VKeyName(e.0), e.1);
      }
    }
    forall e | e in CompileDeps(vdeps, univ)
      ensures e.0 in repo + VarPkgsUniverse(univ) && PlainPfFormula(e.1)
    {
      var src :| src in vdeps && e == (src.0, Compile(src.1, src.0, univ));
      CompilePlain(src.1, src.0, univ);
    }
  }

  // Variable packages drawn from the universe carry variable names.
  lemma VarPartShape(varpart: set<Package>, univ: VarUniverse)
    requires varpart <= VarPkgsUniverse(univ)
    ensures forall p | p in varpart :: p.name.GlobalVarName? || p.name.LocalVarName?
  {
    forall p | p in varpart
      ensures p.name.GlobalVarName? || p.name.LocalVarName?
    {
      var e :| e in univ && p == Package(VKeyName(e.0), e.1);
    }
  }

  // The value the extracted assignment gives to a selected variable.
  lemma AsgOfValue(varpart: set<Package>, p: Package)
    requires VersionUniqueness(varpart)
    requires p in varpart && (p.name.GlobalVarName? || p.name.LocalVarName?)
    ensures KeyOf(p.name) in AsgOf(varpart)
    ensures AsgOf(varpart)[KeyOf(p.name)] == p.version
  {
    var asg := AsgOf(varpart);
    assert KeyOf(p.name) in asg;
    var p2 :| p2 in varpart && (p2.name.GlobalVarName? || p2.name.LocalVarName?)
          && KeyOf(p2.name) == KeyOf(p.name) && asg[KeyOf(p.name)] == p2.version;
    assert VKeyName(KeyOf(p2.name)) == p2.name && VKeyName(KeyOf(p.name)) == p.name;
    assert p2.name == p.name;
    assert p2.version == p.version;  // version uniqueness
  }

  // Conversely, every assigned key comes from a selected variable package.
  lemma AsgOfDomain(varpart: set<Package>, k: VarKey)
    requires VersionUniqueness(varpart)
    requires k in AsgOf(varpart)
    ensures Package(VKeyName(k), AsgOf(varpart)[k]) in varpart
  {
    var asg := AsgOf(varpart);
    var p :| p in varpart && (p.name.GlobalVarName? || p.name.LocalVarName?)
          && KeyOf(p.name) == k;
    AsgOfValue(varpart, p);
    assert VKeyName(KeyOf(p.name)) == p.name;
    assert Package(VKeyName(k), asg[k]) == p;
  }

  // The assignment's packages are exactly the variable packages of the
  // restricted resolution.
  @IsolateAssertions
  lemma AsgPkgsRoundTrip(varpart: set<Package>, univ: VarUniverse)
    requires VersionUniqueness(varpart)
    requires forall p | p in varpart :: p.name.GlobalVarName? || p.name.LocalVarName?
    ensures AsgPkgs(AsgOf(varpart)) == varpart
  {
    hide *;
    reveal AsgPkgs, VKeyName, KeyOf;
    var asg := AsgOf(varpart);
    forall p | p in varpart
      ensures p in AsgPkgs(asg)
    {
      AsgOfValue(varpart, p);
      assert VKeyName(KeyOf(p.name)) == p.name;
      assert Package(VKeyName(KeyOf(p.name)), asg[KeyOf(p.name)]) == p;
    }
    forall q | q in AsgPkgs(asg)
      ensures q in varpart
    {
      var k :| k in asg && q == Package(VKeyName(k), asg[k]);
      AsgOfDomain(varpart, k);
    }
    assert AsgPkgs(asg) == varpart;
  }

  // The extracted assignment respects the universe.
  lemma AsgOfInUniverse(varpart: set<Package>, univ: VarUniverse)
    requires VersionUniqueness(varpart)
    requires varpart <= VarPkgsUniverse(univ)
    ensures AsgInUniverse(AsgOf(varpart), univ)
  {
    var asg := AsgOf(varpart);
    forall k | k in asg
      ensures (k, asg[k]) in univ
    {
      AsgOfDomain(varpart, k);
      var p := Package(VKeyName(k), asg[k]);
      var e :| e in univ && p == Package(VKeyName(e.0), e.1);
      VKeyNameInj(e.0, k);
      assert e == (k, asg[k]);
    }
  }

  // Theorem 4.6.4.
  @IsolateAssertions
  lemma VarReductionSound(repo: set<Package>, vdeps: VFormDepRel, univ: VarUniverse,
                          root: Package, r: set<Package>)
    requires PlainVarInstance(repo, vdeps)
    requires root in repo
    requires ValidResolution(VarReduceRepo(repo, vdeps, univ), VarReduceDeps(vdeps, univ), root, r)
    ensures VersionUniqueness(r * VarPkgsUniverse(univ))
    ensures ValidVarFormResolution(repo, vdeps, root, r * repo,
                                   AsgOf(r * VarPkgsUniverse(univ)))
  {
    var repoX := repo + VarPkgsUniverse(univ);
    var cdeps := CompileDeps(vdeps, univ);
    CompiledInstancePlain(repo, vdeps, univ);
    TseitinLemmas.PfReductionSound(repoX, cdeps, root, r);
    var rpf := r * repoX;
    assert ValidPfResolution(repoX, cdeps, root, rpf);

    var rv := r * repo;
    var varpart := r * VarPkgsUniverse(univ);
    assert rpf == rv + varpart;
    VarPartShape(varpart, univ);
    var asg := AsgOf(varpart);
    AsgPkgsRoundTrip(varpart, univ);
    assert rpf == rv + AsgPkgs(asg);
    AsgOfInUniverse(varpart, univ);

    // Formula closure via the transfer.
    forall e | e in vdeps && e.0 in rv
      ensures VSat(rv, asg, e.0, e.1)
    {
      var ce := (e.0, Compile(e.1, e.0, univ));
      assert ce in cdeps;
      assert e.0 in rpf;
      assert PfSat(rpf, ce.1);
      SatTransfer(rv, asg, univ, e.0, e.1);
    }

    assert root in rv;
  }

  // Theorem 4.6.5.
  @IsolateAssertions
  lemma VarReductionComplete(repo: set<Package>, vdeps: VFormDepRel, univ: VarUniverse,
                             root: Package, rv: set<Package>, asg: Assignment)
    requires PlainVarInstance(repo, vdeps)
    requires AsgInUniverse(asg, univ)
    requires root in repo
    requires ValidVarFormResolution(repo, vdeps, root, rv, asg)
    ensures ValidResolution(VarReduceRepo(repo, vdeps, univ), VarReduceDeps(vdeps, univ),
                            root, VarBuildCore(rv, asg, vdeps, univ))
  {
    var repoX := repo + VarPkgsUniverse(univ);
    var cdeps := CompileDeps(vdeps, univ);
    var rpf := VarBuildPf(rv, asg);
    CompiledInstancePlain(repo, vdeps, univ);

    // rpf is a valid package formula resolution of the compiled instance.
    forall p | p in rpf
      ensures p in repoX
    {
      if p !in rv {
        var k :| k in asg && p == Package(VKeyName(k), asg[k]);
        assert (k, asg[k]) in univ;
      }
    }
    forall p, q | p in rpf && q in rpf && p.name == q.name
      ensures p.version == q.version
    {
      if p !in rv && q !in rv {
        var k1 :| k1 in asg && p == Package(VKeyName(k1), asg[k1]);
        var k2 :| k2 in asg && q == Package(VKeyName(k2), asg[k2]);
        VKeyNameInj(k1, k2);
      } else if p !in rv {
        var k1 :| k1 in asg && p == Package(VKeyName(k1), asg[k1]);
        assert false;  // rv is plain, p's name is a variable name
      } else if q !in rv {
        var k2 :| k2 in asg && q == Package(VKeyName(k2), asg[k2]);
        assert false;
      }
    }
    forall e | e in cdeps && e.0 in rpf
      ensures PfSat(rpf, e.1)
    {
      var src :| src in vdeps && e == (src.0, Compile(src.1, src.0, univ));
      if src.0 !in rv {
        var k :| k in asg && src.0 == Package(VKeyName(k), asg[k]);
        assert false;  // dependers are plain repo packages
      }
      assert VSat(rv, asg, src.0, src.1);
      SatTransfer(rv, asg, univ, src.0, src.1);
    }
    assert ValidPfResolution(repoX, cdeps, root, rpf);

    TseitinLemmas.PfReductionComplete(repoX, cdeps, root, rpf);
  }
}
