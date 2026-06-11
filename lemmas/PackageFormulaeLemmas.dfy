// PackageFormulaeLemmas.dfy — Proofs for §4.5 (partial; see README.md).
//
// We prove that the Package Formula Package Calculus is at least as
// expressive as the core: embedding each core dependency (m, S) as the
// atomic formula (m, S) preserves resolutions exactly. This is the DEP
// rule of Definition 4.5.1(b) coinciding with dependency closure
// (Definition 3.1.3(b)).
//
// The reverse reduction — Definition 4.5.4's Tseitin-style encoding of
// disjunction and negation into synthetic packages, with Theorems 4.5.5
// and 4.5.6 — is not mechanised here.

include "../src/PackageFormulae.dfy"

module PackageFormulaeLemmas {
  import opened Core
  import opened PackageFormulae

  lemma CoreEmbedding(repo: set<Package>, deps: DepRel, root: Package, r: set<Package>)
    ensures ValidResolution(repo, deps, root, r)
        <==> ValidPfResolution(repo, CoreToPf(deps), root, r)
  {
    var pfdeps := CoreToPf(deps);

    if DepClosure(deps, r) {
      forall e | e in pfdeps && e.0 in r
        ensures PfSat(r, e.1)
      {
        var src :| src in deps && e == (src.0, PAtom(src.1.name, src.1.versions));
        var v :| v in src.1.versions && Package(src.1.name, v) in r;
        assert v in e.1.aversions && Package(e.1.aname, v) in r;
      }
      assert PfClosure(pfdeps, r);
    }

    if PfClosure(pfdeps, r) {
      forall e | e in deps && e.0 in r
        ensures exists v :: v in e.1.versions && Package(e.1.name, v) in r
      {
        var red := (e.0, PAtom(e.1.name, e.1.versions));
        assert red in pfdeps;
        assert PfSat(r, red.1);
      }
      assert DepClosure(deps, r);
    }
  }
}
