// VirtualLemmas.dfy — Proofs for §4.7.
//
//   Theorem 4.7.4 (Soundness):   a core resolution of the virtual-reduced
//     instance yields a virtual resolution and provider relation; the
//     intermediate's unique version (injectively) encodes the satisfier,
//     making the selected provider unique.
//   Theorem 4.7.5 (Completeness): a virtual resolution yields a core
//     resolution of the reduced instance, choosing the real satisfier when
//     one is selected and the unique provider otherwise.

include "../src/Virtual.dfy"

module VirtualLemmas {
  import opened Core
  import opened Concurrent
  import opened Virtual

  // Two providers selected (via the extracted π) for the same dependency
  // coincide: the intermediate's version pins the encoding.
  lemma ExtractedPiUnique(r: set<Package>, deps: DepRel, prov: ProvidesRel, enc: EncFn,
                          e: (Package, Dep), q1: Package, q2: Package)
    requires UniqueDepPerName(deps)
    requires Injective(enc)
    requires VersionUniqueness(r)
    requires e in deps
    requires ((e.0, e.1.name), q1) in VirtExtractPi(r, deps, prov, enc)
    requires ((e.0, e.1.name), q2) in VirtExtractPi(r, deps, prov, enc)
    ensures q1 == q2
  {
    var e1, pr1 :| e1 in deps && pr1 in prov && PrMatch(pr1, e1.1)
          && e1.0 in r && Package(PName(e1), enc(pr1.0)) in r
          && ((e1.0, e1.1.name), pr1.0) == ((e.0, e.1.name), q1);
    var e2, pr2 :| e2 in deps && pr2 in prov && PrMatch(pr2, e2.1)
          && e2.0 in r && Package(PName(e2), enc(pr2.0)) in r
          && ((e2.0, e2.1.name), pr2.0) == ((e.0, e.1.name), q2);
    assert e1 == e && e2 == e;  // UniqueDepPerName
    assert Package(PName(e), enc(q1)).name == Package(PName(e), enc(q2)).name;
    assert enc(q1) == enc(q2);  // version uniqueness in r
  }

  // Theorem 4.7.4.
  @IsolateAssertions
  lemma VirtReductionSound(repo: set<Package>, deps: DepRel, prov: ProvidesRel, enc: EncFn,
                           root: Package, r: set<Package>)
    requires PlainVirtualInstance(repo, deps, prov)
    requires WfProvides(repo, prov)
    requires UniqueDepPerName(deps)
    requires Injective(enc)
    requires root in repo
    requires ValidResolution(VirtReduceRepo(repo, deps, prov, enc),
                             VirtReduceDeps(repo, deps, prov, enc), root, r)
    ensures ValidVirtualResolution(repo, deps, prov, root, r * repo,
                                   VirtExtractPi(r, deps, prov, enc))
  {
    var rv := r * repo;
    var pi := VirtExtractPi(r, deps, prov, enc);
    var rdeps := VirtReduceDeps(repo, deps, prov, enc);

    forall e | e in deps && e.0 in rv
      ensures (exists u :: u in e.1.versions && Package(e.1.name, u) in rv)
           || ((exists q | q in rv :: ProviderSelected(e, q, prov, rv, pi))
               && (forall q1, q2 | q1 in rv && q2 in rv
                     && ProviderSelected(e, q1, prov, rv, pi)
                     && ProviderSelected(e, q2, prov, rv, pi) :: q1 == q2))
    {
      if !HasProvider(prov, e.1.name) {
        // The dependency was kept verbatim.
        assert e in VirtKeptEdges(deps, prov);
        var u :| u in e.1.versions && Package(e.1.name, u) in r;
        assert Package(e.1.name, u) !in VirtIntRepo(repo, deps, prov, enc);
        assert Package(e.1.name, u) in rv;
      } else {
        // Follow the intermediate edge to the chosen satisfier.
        var iEdge := (e.0, Dep(PName(e), VirtChoices(repo, prov, e, enc)));
        assert iEdge in VirtIntEdges(repo, deps, prov, enc);
        var w :| w in VirtChoices(repo, prov, e, enc) && Package(PName(e), w) in r;
        if w in VirtRealChoices(repo, e, enc) {
          // A real package satisfies the dependency.
          var u :| u in e.1.versions && Package(e.1.name, u) in repo
                && w == enc(Package(e.1.name, u));
          var rEdge := (Package(PName(e), w), Dep(e.1.name, {u}));
          assert rEdge in VirtRealEdges(repo, deps, prov, enc);
          var u' :| u' in rEdge.1.versions && Package(rEdge.1.name, u') in r;
          assert u' == u;
          assert Package(e.1.name, u) in rv;
        } else {
          // A provider satisfies it, uniquely.
          var pr :| pr in prov && PrMatch(pr, e.1) && w == enc(pr.0);
          var pEdge := (Package(PName(e), w), Dep(pr.0.name, {pr.0.version}));
          assert pEdge in VirtProvEdges(deps, prov, enc);
          var v' :| v' in pEdge.1.versions && Package(pEdge.1.name, v') in r;
          assert Package(pr.0.name, pr.0.version) == pr.0;
          assert pr.0 in r && pr.0 in repo && pr.0 in rv;
          assert ((e.0, e.1.name), pr.0) in pi;
          assert ProviderSelected(e, pr.0, prov, rv, pi);
          forall q1, q2 | q1 in rv && q2 in rv
                && ProviderSelected(e, q1, prov, rv, pi)
                && ProviderSelected(e, q2, prov, rv, pi)
            ensures q1 == q2
          {
            ExtractedPiUnique(r, deps, prov, enc, e, q1, q2);
          }
        }
      }
    }
  }

  // Theorem 4.7.5.
  @IsolateAssertions
  lemma VirtReductionComplete(repo: set<Package>, deps: DepRel, prov: ProvidesRel, enc: EncFn,
                              root: Package, rv: set<Package>, pi: ProviderRel)
    requires PlainVirtualInstance(repo, deps, prov)
    requires WfProvides(repo, prov)
    requires UniqueDepPerName(deps)
    requires Injective(enc)
    requires root in repo
    requires ValidVirtualResolution(repo, deps, prov, root, rv, pi)
    ensures ValidResolution(VirtReduceRepo(repo, deps, prov, enc),
                            VirtReduceDeps(repo, deps, prov, enc),
                            root, VirtBuildCore(rv, pi, deps, prov, enc))
  {
    var r := VirtBuildCore(rv, pi, deps, prov, enc);

    // r ⊆ reduced repo.
    forall p | p in r
      ensures p in VirtReduceRepo(repo, deps, prov, enc)
    {
      if p in rv {
        assert p in repo;
      } else if p in VirtIntReal(rv, deps, prov, enc) {
        var e, u :| e in deps && HasProvider(prov, e.1.name) && e.0 in rv
              && u in e.1.versions && Package(e.1.name, u) in rv
              && p == Package(PName(e), enc(Package(e.1.name, u)));
        assert enc(Package(e.1.name, u)) in VirtRealChoices(repo, e, enc);
        assert p in VirtIntRepo(repo, deps, prov, enc);
      } else {
        var e, q :| e in deps && HasProvider(prov, e.1.name) && e.0 in rv
              && (forall u | u in e.1.versions :: Package(e.1.name, u) !in rv)
              && q in rv && ProviderSelected(e, q, prov, rv, pi)
              && p == Package(PName(e), enc(q));
        var pr :| pr in prov && pr.0 == q && PrMatch(pr, e.1);
        assert enc(q) in VirtProvChoices(prov, e, enc);
        assert p in VirtIntRepo(repo, deps, prov, enc);
      }
    }

    // Version uniqueness.
    forall p, q | p in r && q in r && p.name == q.name
      ensures p.version == q.version
    {
      if p in rv && q in rv {
        // uniqueness of rv
      } else if p in rv {
        IntHasProviderName(rv, pi, deps, prov, enc, q);
        assert !p.name.ProviderName?;
        assert false;
      } else if q in rv {
        IntHasProviderName(rv, pi, deps, prov, enc, p);
        assert !q.name.ProviderName?;
        assert false;
      } else {
        IntUnique(rv, pi, deps, prov, enc, p, q);
      }
    }

    // Dependency closure over the four groups of reduced edges.
    forall ed | ed in VirtReduceDeps(repo, deps, prov, enc) && ed.0 in r
      ensures exists v :: v in ed.1.versions && Package(ed.1.name, v) in r
    {
      if ed in VirtKeptEdges(deps, prov) {
        assert ed in deps && !HasProvider(prov, ed.1.name);
        SourceInRv(rv, pi, deps, prov, enc, repo, ed.0);
        // The provider branch is impossible without a provider for the name.
        if exists u :: u in ed.1.versions && Package(ed.1.name, u) in rv {
          var u :| u in ed.1.versions && Package(ed.1.name, u) in rv;
        } else {
          var q :| q in rv && ProviderSelected(ed, q, prov, rv, pi);
          var pr :| pr in prov && pr.0 == q && PrMatch(pr, ed.1);
          assert HasProvider(prov, ed.1.name);
          assert false;
        }
      } else if ed in VirtIntEdges(repo, deps, prov, enc) {
        var e :| e in deps && HasProvider(prov, e.1.name)
              && ed == (e.0, Dep(PName(e), VirtChoices(repo, prov, e, enc)));
        SourceInRv(rv, pi, deps, prov, enc, repo, e.0);
        if exists u :: u in e.1.versions && Package(e.1.name, u) in rv {
          var u :| u in e.1.versions && Package(e.1.name, u) in rv;
          assert Package(PName(e), enc(Package(e.1.name, u))) in VirtIntReal(rv, deps, prov, enc);
          assert enc(Package(e.1.name, u)) in VirtRealChoices(repo, e, enc);
        } else {
          var q :| q in rv && ProviderSelected(e, q, prov, rv, pi);
          assert Package(PName(e), enc(q)) in VirtIntProv(rv, pi, deps, prov, enc);
          var pr :| pr in prov && pr.0 == q && PrMatch(pr, e.1);
          assert enc(q) in VirtProvChoices(prov, e, enc);
        }
      } else if ed in VirtRealEdges(repo, deps, prov, enc) {
        var e, u :| e in deps && HasProvider(prov, e.1.name)
              && u in e.1.versions && Package(e.1.name, u) in repo
              && ed == (Package(PName(e), enc(Package(e.1.name, u))), Dep(e.1.name, {u}));
        IntDecodesTo(rv, pi, deps, prov, enc, e, Package(e.1.name, u));
        assert Package(e.1.name, u) in rv;
        assert u in ed.1.versions && Package(ed.1.name, u) in r;
      } else {
        assert ed in VirtProvEdges(deps, prov, enc);
        var e, pr :| e in deps && HasProvider(prov, e.1.name)
              && pr in prov && PrMatch(pr, e.1)
              && ed == (Package(PName(e), enc(pr.0)), Dep(pr.0.name, {pr.0.version}));
        IntDecodesTo(rv, pi, deps, prov, enc, e, pr.0);
        assert pr.0 in rv;
        assert Package(pr.0.name, pr.0.version) == pr.0;
        assert pr.0.version in ed.1.versions && Package(ed.1.name, pr.0.version) in r;
      }
    }
  }

  // Intermediates carry ProviderName names.
  lemma IntHasProviderName(rv: set<Package>, pi: ProviderRel, deps: DepRel,
                           prov: ProvidesRel, enc: EncFn, p: Package)
    requires p in VirtBuildCore(rv, pi, deps, prov, enc) && p !in rv
    ensures p.name.ProviderName?
  {
    if p in VirtIntReal(rv, deps, prov, enc) {
      var e, u :| e in deps && HasProvider(prov, e.1.name) && e.0 in rv
            && u in e.1.versions && Package(e.1.name, u) in rv
            && p == Package(PName(e), enc(Package(e.1.name, u)));
    } else {
      var e, q :| e in deps && HasProvider(prov, e.1.name) && e.0 in rv
            && (forall u | u in e.1.versions :: Package(e.1.name, u) !in rv)
            && q in rv && ProviderSelected(e, q, prov, rv, pi)
            && p == Package(PName(e), enc(q));
    }
  }

  // Two intermediates with the same name have the same version: the real
  // and provider parts are mutually exclusive, and each is functional.
  lemma IntUnique(rv: set<Package>, pi: ProviderRel, deps: DepRel,
                  prov: ProvidesRel, enc: EncFn, p: Package, q: Package)
    requires UniqueDepPerName(deps)
    requires VersionUniqueness(rv)
    requires VirtClosure(deps, prov, rv, pi)
    requires p in VirtBuildCore(rv, pi, deps, prov, enc) && p !in rv
    requires q in VirtBuildCore(rv, pi, deps, prov, enc) && q !in rv
    requires p.name == q.name
    ensures p.version == q.version
  {
    if p in VirtIntReal(rv, deps, prov, enc) && q in VirtIntReal(rv, deps, prov, enc) {
      var e1, u1 :| e1 in deps && HasProvider(prov, e1.1.name) && e1.0 in rv
            && u1 in e1.1.versions && Package(e1.1.name, u1) in rv
            && p == Package(PName(e1), enc(Package(e1.1.name, u1)));
      var e2, u2 :| e2 in deps && HasProvider(prov, e2.1.name) && e2.0 in rv
            && u2 in e2.1.versions && Package(e2.1.name, u2) in rv
            && q == Package(PName(e2), enc(Package(e2.1.name, u2)));
      assert e1.0 == e2.0 && e1.1.name == e2.1.name;
      assert e1 == e2;   // UniqueDepPerName
      assert u1 == u2;   // version uniqueness of rv on the dependee name
    } else if p in VirtIntProv(rv, pi, deps, prov, enc) && q in VirtIntProv(rv, pi, deps, prov, enc) {
      var e1, q1 :| e1 in deps && HasProvider(prov, e1.1.name) && e1.0 in rv
            && (forall u | u in e1.1.versions :: Package(e1.1.name, u) !in rv)
            && q1 in rv && ProviderSelected(e1, q1, prov, rv, pi)
            && p == Package(PName(e1), enc(q1));
      var e2, q2 :| e2 in deps && HasProvider(prov, e2.1.name) && e2.0 in rv
            && (forall u | u in e2.1.versions :: Package(e2.1.name, u) !in rv)
            && q2 in rv && ProviderSelected(e2, q2, prov, rv, pi)
            && q == Package(PName(e2), enc(q2));
      assert e1.0 == e2.0 && e1.1.name == e2.1.name;
      assert e1 == e2;   // UniqueDepPerName
      // The real branch fails for e1, so the provider branch's uniqueness
      // conjunct applies.
      assert !(exists u :: u in e1.1.versions && Package(e1.1.name, u) in rv);
      assert q1 == q2;
    } else if p in VirtIntReal(rv, deps, prov, enc) {
      var e1, u1 :| e1 in deps && HasProvider(prov, e1.1.name) && e1.0 in rv
            && u1 in e1.1.versions && Package(e1.1.name, u1) in rv
            && p == Package(PName(e1), enc(Package(e1.1.name, u1)));
      var e2, q2 :| e2 in deps && HasProvider(prov, e2.1.name) && e2.0 in rv
            && (forall u | u in e2.1.versions :: Package(e2.1.name, u) !in rv)
            && q2 in rv && ProviderSelected(e2, q2, prov, rv, pi)
            && q == Package(PName(e2), enc(q2));
      assert e1 == e2;  // UniqueDepPerName
      assert false;     // real satisfier both selected and excluded
    } else {
      var e1, q1 :| e1 in deps && HasProvider(prov, e1.1.name) && e1.0 in rv
            && (forall u | u in e1.1.versions :: Package(e1.1.name, u) !in rv)
            && q1 in rv && ProviderSelected(e1, q1, prov, rv, pi)
            && p == Package(PName(e1), enc(q1));
      var e2, u2 :| e2 in deps && HasProvider(prov, e2.1.name) && e2.0 in rv
            && u2 in e2.1.versions && Package(e2.1.name, u2) in rv
            && q == Package(PName(e2), enc(Package(e2.1.name, u2)));
      assert e1 == e2;  // UniqueDepPerName
      assert false;
    }
  }

  // The source of a kept or intermediate edge is an original package of rv.
  lemma SourceInRv(rv: set<Package>, pi: ProviderRel, deps: DepRel,
                   prov: ProvidesRel, enc: EncFn, repo: set<Package>, p: Package)
    requires forall q | q in rv :: q in repo
    requires forall q | q in repo :: !q.name.ProviderName?
    requires !p.name.ProviderName?
    requires p in VirtBuildCore(rv, pi, deps, prov, enc)
    ensures p in rv
  {
    if p !in rv {
      IntHasProviderName(rv, pi, deps, prov, enc, p);
      assert false;
    }
  }

  // An intermediate of dependency e present in the built resolution at the
  // encoding of package x means x is the selected satisfier, in rv.
  lemma IntDecodesTo(rv: set<Package>, pi: ProviderRel, deps: DepRel,
                     prov: ProvidesRel, enc: EncFn, e: (Package, Dep), x: Package)
    requires UniqueDepPerName(deps)
    requires Injective(enc)
    requires forall q | q in rv :: !q.name.ProviderName?
    requires e in deps
    requires Package(PName(e), enc(x)) in VirtBuildCore(rv, pi, deps, prov, enc)
    ensures x in rv
  {
    var p := Package(PName(e), enc(x));
    assert p !in rv;  // rv carries no ProviderName packages
    if p in VirtIntReal(rv, deps, prov, enc) {
      var e1, u1 :| e1 in deps && HasProvider(prov, e1.1.name) && e1.0 in rv
            && u1 in e1.1.versions && Package(e1.1.name, u1) in rv
            && p == Package(PName(e1), enc(Package(e1.1.name, u1)));
      assert e1 == e;  // UniqueDepPerName
      assert Package(e.1.name, u1) == x;  // injectivity
    } else {
      var e1, q1 :| e1 in deps && HasProvider(prov, e1.1.name) && e1.0 in rv
            && (forall u | u in e1.1.versions :: Package(e1.1.name, u) !in rv)
            && q1 in rv && ProviderSelected(e1, q1, prov, rv, pi)
            && p == Package(PName(e1), enc(q1));
      assert e1 == e;  // UniqueDepPerName
      assert q1 == x;  // injectivity
    }
  }
}
