// Virtual.dfy — The Virtual Package Calculus (§4.7).
//
// Definitions 4.7.1–4.7.3 of the paper, modelling APT-style virtual
// packages: a provides-entry (q, (m, w)) says package q provides name m
// at version w (or at the wildcard ∗, matching any version set). A
// dependency on m is satisfied either by a real package (m, u) or by a
// unique selected provider, witnessed by a provider relation.
//
// Mechanisation notes:
//   - the paper's provider relation is π ⊆ P × P; we key it by the
//     dependency, π ⊆ (P × N) × P, so that "exactly one provider" is
//     expressible per dependency (with π ⊆ P × P, a provider selected for
//     one dependency of p can alias a provider of another dependency,
//     muddying the paper's ∃! reading);
//   - the reduction's intermediate packages ⟨p, m⟩ use *versions* that
//     encode the chosen satisfier (Figure D.2's ⟨B, 1⟩-style versions);
//     since Core.Version is nat, the reduction takes an injective
//     enc : P → V as a parameter;
//   - as in §4.2/§4.3, intermediate names are keyed by (depender,
//     dependee name), so UniqueDepPerName is required;
//   - `prov` abbreviates the provides relation (`provides` is a Dafny
//     keyword).
//
// Theorems 4.7.4 and 4.7.5 are proved in lemmas/VirtualLemmas.dfy.

include "Core.dfy"
include "Concurrent.dfy"

module Virtual {
  import opened Core
  import opened Concurrent

  // Definition 4.7.1: w ∈ V ∪ {∗}.
  datatype ProvVer = Exact(v: Version) | Wild

  // The provides relation ⊆ P × (N × (V ∪ {∗})).
  type ProvidesRel = set<(Package, (Name, ProvVer))>

  // The provider relation: ((depender, dependee name), provider).
  type ProviderRel = set<((Package, Name), Package)>

  // Does provides-entry pr satisfy dependency target d?
  predicate PrMatch(pr: (Package, (Name, ProvVer)), d: Dep) {
    pr.1.0 == d.name && (pr.1.1.Wild? || pr.1.1.v in d.versions)
  }

  // Package q provides a match for d.
  predicate ProvidesMatch(prov: ProvidesRel, q: Package, d: Dep) {
    exists pr | pr in prov :: pr.0 == q && PrMatch(pr, d)
  }

  predicate HasProvider(prov: ProvidesRel, n: Name) {
    exists pr | pr in prov :: pr.1.0 == n
  }

  // A provider for dependency e is selected in (r, π).
  predicate ProviderSelected(e: (Package, Dep), q: Package,
                             prov: ProvidesRel, r: set<Package>, pi: ProviderRel) {
    q in r && ProvidesMatch(prov, q, e.1) && ((e.0, e.1.name), q) in pi
  }

  // Definition 4.7.2(b): each dependency is satisfied by a real package or
  // by exactly one selected provider.
  predicate VirtClosure(deps: DepRel, prov: ProvidesRel,
                        r: set<Package>, pi: ProviderRel) {
    forall e | e in deps && e.0 in r ::
      (exists u :: u in e.1.versions && Package(e.1.name, u) in r)
      || ((exists q | q in r :: ProviderSelected(e, q, prov, r, pi))
          && (forall q1, q2 | q1 in r && q2 in r
                && ProviderSelected(e, q1, prov, r, pi)
                && ProviderSelected(e, q2, prov, r, pi) :: q1 == q2))
  }

  // Definition 4.7.2: (r, π) ∈ S_P(D, Provides, root).
  predicate ValidVirtualResolution(repo: set<Package>, deps: DepRel, prov: ProvidesRel,
                                   root: Package, r: set<Package>, pi: ProviderRel) {
    r <= repo
    && RootInclusion(root, r)
    && VirtClosure(deps, prov, r, pi)
    && VersionUniqueness(r)
  }

  // Definition 4.7.1's side condition: providers exist.
  predicate WfProvides(repo: set<Package>, prov: ProvidesRel) {
    forall pr | pr in prov :: pr.0 in repo
  }

  // Freshness: no synthetic provider-intermediate names in the instance.
  predicate PlainVirtualInstance(repo: set<Package>, deps: DepRel, prov: ProvidesRel) {
    (forall p | p in repo :: !p.name.ProviderName?)
    && (forall e | e in deps :: e.0 in repo && !e.1.name.ProviderName?)
    && (forall pr | pr in prov :: !pr.1.0.ProviderName?)
  }

  // ---------------------------------------------------------------------
  // The reduction to the core (Definition 4.7.3), parameterised by an
  // injective encoding of packages as versions.
  // ---------------------------------------------------------------------

  type EncFn = Package -> Version

  ghost predicate Injective(enc: EncFn) {
    forall p1, p2 :: enc(p1) == enc(p2) ==> p1 == p2
  }

  // The intermediate package name ⟨p, m⟩.
  function PName(e: (Package, Dep)): Name {
    ProviderName(e.0, e.1.name)
  }

  // The versions of ⟨p, m⟩: one per real satisfier, one per matching
  // provider.
  function VirtRealChoices(repo: set<Package>, e: (Package, Dep), enc: EncFn): set<Version> {
    set u | u in e.1.versions && Package(e.1.name, u) in repo :: enc(Package(e.1.name, u))
  }

  function VirtProvChoices(prov: ProvidesRel, e: (Package, Dep), enc: EncFn): set<Version> {
    set pr | pr in prov && PrMatch(pr, e.1) :: enc(pr.0)
  }

  function VirtChoices(repo: set<Package>, prov: ProvidesRel,
                       e: (Package, Dep), enc: EncFn): set<Version> {
    VirtRealChoices(repo, e, enc) + VirtProvChoices(prov, e, enc)
  }

  // (a): the repository gains the intermediates of provider-relevant deps.
  function VirtIntRepo(repo: set<Package>, deps: DepRel, prov: ProvidesRel, enc: EncFn): set<Package> {
    set e, w | e in deps && HasProvider(prov, e.1.name)
      && w in VirtChoices(repo, prov, e, enc)
      :: Package(PName(e), w)
  }

  function VirtReduceRepo(repo: set<Package>, deps: DepRel, prov: ProvidesRel, enc: EncFn): set<Package> {
    repo + VirtIntRepo(repo, deps, prov, enc)
  }

  // (b): dependencies on provider-less names are kept; the rest are
  // routed through the intermediate, whose version selects the satisfier.
  function VirtKeptEdges(deps: DepRel, prov: ProvidesRel): DepRel {
    set e | e in deps && !HasProvider(prov, e.1.name) :: e
  }

  function VirtIntEdges(repo: set<Package>, deps: DepRel, prov: ProvidesRel, enc: EncFn): DepRel {
    set e | e in deps && HasProvider(prov, e.1.name) ::
      (e.0, Dep(PName(e), VirtChoices(repo, prov, e, enc)))
  }

  function VirtRealEdges(repo: set<Package>, deps: DepRel, prov: ProvidesRel, enc: EncFn): DepRel {
    set e, u | e in deps && HasProvider(prov, e.1.name)
      && u in e.1.versions && Package(e.1.name, u) in repo ::
      (Package(PName(e), enc(Package(e.1.name, u))), Dep(e.1.name, {u}))
  }

  function VirtProvEdges(deps: DepRel, prov: ProvidesRel, enc: EncFn): DepRel {
    set e, pr | e in deps && HasProvider(prov, e.1.name)
      && pr in prov && PrMatch(pr, e.1) ::
      (Package(PName(e), enc(pr.0)), Dep(pr.0.name, {pr.0.version}))
  }

  function VirtReduceDeps(repo: set<Package>, deps: DepRel, prov: ProvidesRel, enc: EncFn): DepRel {
    VirtKeptEdges(deps, prov)
    + VirtIntEdges(repo, deps, prov, enc)
    + VirtRealEdges(repo, deps, prov, enc)
    + VirtProvEdges(deps, prov, enc)
  }

  // ---------------------------------------------------------------------
  // The constructions of Theorems 4.7.4 and 4.7.5.
  // ---------------------------------------------------------------------

  // Theorem 4.7.4: the provider relation read off the intermediates'
  // selected versions.
  function VirtExtractPi(r: set<Package>, deps: DepRel, prov: ProvidesRel, enc: EncFn): ProviderRel {
    set e, pr | e in deps && pr in prov && PrMatch(pr, e.1)
      && e.0 in r && Package(PName(e), enc(pr.0)) in r
      :: ((e.0, e.1.name), pr.0)
  }

  // Theorem 4.7.5: the original resolution plus one intermediate per
  // provider-relevant dependency of a selected package — at the real
  // satisfier when one is selected, else at the selected provider.
  function VirtIntReal(rv: set<Package>, deps: DepRel, prov: ProvidesRel, enc: EncFn): set<Package> {
    set e, u | e in deps && HasProvider(prov, e.1.name) && e.0 in rv
      && u in e.1.versions && Package(e.1.name, u) in rv
      :: Package(PName(e), enc(Package(e.1.name, u)))
  }

  function VirtIntProv(rv: set<Package>, pi: ProviderRel, deps: DepRel,
                       prov: ProvidesRel, enc: EncFn): set<Package> {
    set e, q | e in deps && HasProvider(prov, e.1.name) && e.0 in rv
      && (forall u | u in e.1.versions :: Package(e.1.name, u) !in rv)
      && q in rv && ProviderSelected(e, q, prov, rv, pi)
      :: Package(PName(e), enc(q))
  }

  function VirtBuildCore(rv: set<Package>, pi: ProviderRel, deps: DepRel,
                         prov: ProvidesRel, enc: EncFn): set<Package> {
    rv + VirtIntReal(rv, deps, prov, enc) + VirtIntProv(rv, pi, deps, prov, enc)
  }
}
