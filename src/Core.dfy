// Core.dfy — The Package Calculus, core definitions.
//
// Formalises §3.1 of "Package Managers à la Carte: A Formal Model of
// Dependency Resolution" (Gibb, Ferris, Allsopp, Gazagnaire, Madhavapeddy;
// arXiv:2602.18602v1).
//
// All predicates here are compilable (non-ghost), which witnesses the
// NP-membership half of Theorem 3.1.4: a candidate resolution can be
// checked mechanically (see also lemmas/ and the exhaustive resolver in
// src/Solver.dfy).

module Core {
  // Definition 3.1.1(b): an abstract set of versions. We fix naturals,
  // which also provides the total ordering required by Definition 3.2.1.
  type Version = nat

  // Definition 3.1.1(a): the set of possible package names.
  //
  // `Atom` covers ordinary ecosystem names. The remaining constructors are
  // the synthetic names introduced by the paper's reductions; making them
  // datatype constructors gives us, for free, the freshness and injectivity
  // properties the reductions rely on:
  //   - RootName / VarName / ClauseName: the 3-SAT hardness construction
  //     of Appendix B (Theorem 3.1.4);
  //   - ConflictName: the synthetic conflict package kappa_{p,(m,S)} of the
  //     conflict reduction (Definition 4.1.3);
  //   - GranularName / IntermediateName: the granular packages ⟨n, γ⟩ and
  //     intermediate packages ⟨n, v, m⟩ of the concurrent versions and peer
  //     dependency reductions (Definitions 4.2.3 and 4.3.3);
  //   - FeatureName: the feature packages ⟨n, f⟩ of the feature reduction
  //     (Definition 4.4.4);
  //   - ProviderName: the intermediate packages ⟨p, m⟩ of the virtual
  //     package reduction (Definition 4.7.3);
  //   - OrName / NegName: the Tseitin-style disjunction packages and the
  //     negated-atom conflict packages of the package formula reduction
  //     (Definition 4.5.4). These embed formulae in names, so PFormula is
  //     declared here, mutually recursive with Name.
  datatype Name =
    | Atom(id: string)
    | RootName
    | VarName(varIdx: nat)
    | ClauseName(clauseIdx: nat)
    | ConflictName(decl: Package, target: Name, scope: set<Version>)
    | GranularName(gbase: Name, gran: nat)
    | IntermediateName(idepender: Package, idep: Name)
    | FeatureName(fbase: Name, feat: string)
    | ProviderName(vdepender: Package, vname: Name)
    | OrName(oleft: PFormula, oright: PFormula)
    | NegName(nbase: Name, nscope: set<Version>)

  // Definition 4.5.1(a): package formulae ψ ::= (m, S) | ψ∧ψ | ψ∨ψ | ¬ψ.
  // Declared here (rather than in PackageFormulae) because the reduction's
  // synthetic names carry subformulae.
  datatype PFormula =
    | PAtom(aname: Name, aversions: set<Version>)
    | PAnd(cleft: PFormula, cright: PFormula)
    | POr(dleft: PFormula, dright: PFormula)
    | PNot(inner: PFormula)

  // Definition 3.1.1(c): P = N × V, packages as name-version pairs.
  datatype Package = Package(name: Name, version: Version)

  // A dependency target: a package name together with the set of versions
  // that can satisfy the dependency.
  datatype Dep = Dep(name: Name, versions: set<Version>)

  // Definition 3.1.2: the dependency relation D ⊆ P × (N × ℘(V)).
  type DepRel = set<(Package, Dep)>

  // Definition 3.1.2, side condition: every package referenced by D must
  // exist (be in the repository R ⊆ P).
  predicate WfDeps(repo: set<Package>, deps: DepRel) {
    forall e | e in deps ::
      e.0 in repo && forall v | v in e.1.versions :: Package(e.1.name, v) in repo
  }

  // Definition 3.1.3(a): the resolution contains the root.
  predicate RootInclusion(root: Package, r: set<Package>) {
    root in r
  }

  // Definition 3.1.3(b): for every package in the resolution, each of its
  // dependencies is satisfied by a compatible version in the resolution.
  predicate DepClosure(deps: DepRel, r: set<Package>) {
    forall e | e in deps && e.0 in r ::
      exists v :: v in e.1.versions && Package(e.1.name, v) in r
  }

  // Definition 3.1.3(c): only one version of a package name is in the
  // resolution.
  predicate VersionUniqueness(r: set<Package>) {
    forall p, q | p in r && q in r && p.name == q.name :: p.version == q.version
  }

  // Definition 3.1.3: r ∈ S(D, root), a valid resolution drawn from repo.
  predicate ValidResolution(repo: set<Package>, deps: DepRel, root: Package, r: set<Package>) {
    r <= repo
    && RootInclusion(root, r)
    && DepClosure(deps, r)
    && VersionUniqueness(r)
  }

  // The query Q ⊆ N × ℘(V): the immediate dependencies of the root
  // (Definition 3.1.3, final remark).
  function Query(deps: DepRel, root: Package): set<Dep> {
    set e | e in deps && e.0 == root :: e.1
  }

  // 𝒱_n (Definition 3.2.3(b)): the versions of name n that exist in repo.
  function VersionsOf(repo: set<Package>, n: Name): set<Version> {
    set p | p in repo && p.name == n :: p.version
  }
}
