// SingularLemmas.dfy — Proofs for §4.9.
//
// Singular dependencies are a restriction of the core calculus: every
// singular instance embeds into the core via singleton version sets,
// preserving resolutions exactly. (The paper notes the converse fails —
// the core cannot be reduced to singular dependencies — since singular
// dependencies cannot express version choice; that is an expressivity
// claim about all possible reductions and is not mechanised.)

include "../src/Singular.dfy"

module SingularLemmas {
  import opened Core
  import opened Singular

  lemma SingularEmbedding(repo: set<Package>, sdeps: SingularRel, root: Package, r: set<Package>)
    ensures ValidSingularResolution(repo, sdeps, root, r)
        <==> ValidResolution(repo, SingularToCore(sdeps), root, r)
  {
    var deps := SingularToCore(sdeps);

    if SingularClosure(sdeps, r) {
      forall e | e in deps && e.0 in r
        ensures exists v :: v in e.1.versions && Package(e.1.name, v) in r
      {
        var src :| src in sdeps && e == (src.0, Dep(src.1.name, {src.1.version}));
        assert src.1 == Package(src.1.name, src.1.version);
        assert src.1.version in e.1.versions && Package(e.1.name, src.1.version) in r;
      }
      assert DepClosure(deps, r);
    }

    if DepClosure(deps, r) {
      forall e | e in sdeps && e.0 in r
        ensures e.1 in r
      {
        var red := (e.0, Dep(e.1.name, {e.1.version}));
        assert red in deps;
        var v :| v in red.1.versions && Package(red.1.name, v) in r;
        assert v == e.1.version;
        assert e.1 == Package(e.1.name, e.1.version);
      }
      assert SingularClosure(sdeps, r);
    }
  }
}
