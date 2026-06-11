// PackageFormulae.dfy — The Package Formula Package Calculus (§4.5).
//
// Definitions 4.5.1–4.5.4 of the paper: boolean formulae over package
// dependencies, e.g. opam's ("lwt" | "async") or APT's
// `Depends: libssl-dev | libgnutls-dev`. The PFormula datatype itself
// lives in Core, mutually recursive with Name, because the reduction's
// synthetic packages carry subformulae in their names.
//
// The reduction (Definition 4.5.4) uses one synthetic package per
// disjunction subformula — a Tseitin auxiliary variable with two versions,
// one per disjunct — keeping the reduction linear in the formula size, and
// the conflict encoding of §4.1 for negated atoms. Negation is pushed
// inward by De Morgan's laws, implemented here as a polarity flag.
//
// lemmas/PackageFormulaeLemmas.dfy proves the core-to-formula embedding;
// the general soundness/completeness theorems for this reduction
// (Theorems 4.5.5/4.5.6) are not mechanised, but tests/Extensions.dfy
// checks both directions exhaustively on the paper's Figure D.1 instance.

include "Core.dfy"

module PackageFormulae {
  import opened Core

  // Definition 4.5.2: package formula dependencies D_ψ ⊆ P × Ψ.
  type PfDepRel = set<(Package, PFormula)>

  // Definition 4.5.1(b): the satisfaction relation r ⊨ ψ
  // (rules DEP, AND, OR-L/OR-R, NOT).
  predicate PfSat(r: set<Package>, f: PFormula) {
    match f
    case PAtom(n, vs) => exists v :: v in vs && Package(n, v) in r
    case PAnd(a, b) => PfSat(r, a) && PfSat(r, b)
    case POr(a, b) => PfSat(r, a) || PfSat(r, b)
    case PNot(g) => !PfSat(r, g)
  }

  // Definition 4.5.3(b): formula closure.
  predicate PfClosure(pfdeps: PfDepRel, r: set<Package>) {
    forall e | e in pfdeps && e.0 in r :: PfSat(r, e.1)
  }

  // Definition 4.5.3: r ∈ S_ψ(D_ψ, root).
  predicate ValidPfResolution(repo: set<Package>, pfdeps: PfDepRel, root: Package, r: set<Package>) {
    r <= repo
    && RootInclusion(root, r)
    && PfClosure(pfdeps, r)
    && VersionUniqueness(r)
  }

  // Embedding of the core calculus: each dependency (m, S) becomes the
  // atomic formula (m, S).
  function CoreToPf(deps: DepRel): PfDepRel {
    set e | e in deps :: (e.0, PAtom(e.1.name, e.1.versions))
  }

  // ---------------------------------------------------------------------
  // The reduction to the core (Definition 4.5.4).
  // ---------------------------------------------------------------------

  function FSize(f: PFormula): nat {
    match f
    case PAtom(_, _) => 1
    case PAnd(a, b) => 1 + FSize(a) + FSize(b)
    case POr(a, b) => 1 + FSize(a) + FSize(b)
    case PNot(g) => 1 + FSize(g)
  }

  // The dependency targets a package satisfying ψ (under polarity `neg`)
  // must require. Negation is pushed inward: ¬(a∧b) becomes the
  // disjunction package of (¬a ∨ ¬b) (Definition 4.5.4(b)(iv)), ¬¬ψ
  // becomes ψ ((b)(v)), and a negated atom becomes a dependency on its
  // conflict package at version 1 ((b)(vi)).
  function EncTargets(f: PFormula, neg: bool): set<Dep>
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
      if !neg then {Dep(n, vs)}                       // (b)(i)
      else {Dep(NegName(n, vs), {1 as Version})}      // (b)(vi)
    case PAnd(a, b) =>
      if !neg then EncTargets(a, false) + EncTargets(b, false)   // (b)(ii)
      else {Dep(OrName(PNot(a), PNot(b)), {0 as Version, 1 as Version})}  // (b)(iv)
    case POr(a, b) =>
      if !neg then {Dep(OrName(a, b), {0 as Version, 1 as Version})}      // (b)(iii)
      else EncTargets(a, true) + EncTargets(b, true)             // (b)(iv)
    case PNot(g) => EncTargets(g, !neg)                          // (b)(v)
  }

  // The global auxiliary edges: each disjunction package's version selects
  // a disjunct, and each conflicting package of a negated atom requires
  // the conflict package at version 0.
  function EncAuxEdges(f: PFormula, neg: bool): DepRel
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
      if !neg then {}
      else set u | u in vs :: (Package(n, u), Dep(NegName(n, vs), {0 as Version}))
    case PAnd(a, b) =>
      if !neg then EncAuxEdges(a, false) + EncAuxEdges(b, false)
      else
        var orn := OrName(PNot(a), PNot(b));
        (set t | t in EncTargets(a, true) :: (Package(orn, 0), t))
        + (set t | t in EncTargets(b, true) :: (Package(orn, 1), t))
        + EncAuxEdges(a, true) + EncAuxEdges(b, true)
    case POr(a, b) =>
      if !neg then
        var orn := OrName(a, b);
        (set t | t in EncTargets(a, false) :: (Package(orn, 0), t))
        + (set t | t in EncTargets(b, false) :: (Package(orn, 1), t))
        + EncAuxEdges(a, false) + EncAuxEdges(b, false)
      else EncAuxEdges(a, true) + EncAuxEdges(b, true)
    case PNot(g) => EncAuxEdges(g, !neg)
  }

  // The synthetic packages: two versions per disjunction subformula
  // ((a)(iii)) and per negated atom ((a)(iv)).
  function EncAuxRepo(f: PFormula, neg: bool): set<Package>
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
      if !neg then {}
      else {Package(NegName(n, vs), 0), Package(NegName(n, vs), 1)}
    case PAnd(a, b) =>
      if !neg then EncAuxRepo(a, false) + EncAuxRepo(b, false)
      else
        var orn := OrName(PNot(a), PNot(b));
        {Package(orn, 0), Package(orn, 1)} + EncAuxRepo(a, true) + EncAuxRepo(b, true)
    case POr(a, b) =>
      if !neg then
        var orn := OrName(a, b);
        {Package(orn, 0), Package(orn, 1)} + EncAuxRepo(a, false) + EncAuxRepo(b, false)
      else EncAuxRepo(a, true) + EncAuxRepo(b, true)
    case PNot(g) => EncAuxRepo(g, !neg)
  }

  // Definition 4.5.4(a).
  function PfReduceRepo(repo: set<Package>, pfdeps: PfDepRel): set<Package> {
    repo + set e, p | e in pfdeps && p in EncAuxRepo(e.1, false) :: p
  }

  // Definition 4.5.4(b): each depender requires its formula's targets,
  // plus the global auxiliary edges.
  function PfReduceDeps(pfdeps: PfDepRel): DepRel {
    (set e, t | e in pfdeps && t in EncTargets(e.1, false) :: (e.0, t))
    + (set e, ed | e in pfdeps && ed in EncAuxEdges(e.1, false) :: ed)
  }

  // Freshness: the instance mentions no Tseitin packages, and dependers
  // exist.
  predicate PlainPfFormula(f: PFormula) {
    match f
    case PAtom(n, _) => !n.OrName? && !n.NegName?
    case PAnd(a, b) => PlainPfFormula(a) && PlainPfFormula(b)
    case POr(a, b) => PlainPfFormula(a) && PlainPfFormula(b)
    case PNot(g) => PlainPfFormula(g)
  }

  predicate PlainPfInstance(repo: set<Package>, pfdeps: PfDepRel) {
    (forall p | p in repo :: !p.name.OrName? && !p.name.NegName?)
    && (forall e | e in pfdeps :: e.0 in repo && PlainPfFormula(e.1))
  }

  // Every dependency target in ts is satisfied in r.
  predicate TargetsSatisfied(r: set<Package>, ts: set<Dep>) {
    forall t | t in ts :: exists v :: v in t.versions && Package(t.name, v) in r
  }

  // ---------------------------------------------------------------------
  // The construction of Theorem 4.5.6: witness sets.
  // ---------------------------------------------------------------------

  // The witness set W(ψ) of Theorem 4.5.6, with De Morgan's laws realised
  // as a polarity flag: the synthetic packages that accompany a resolution
  // satisfying ψ (or, at negative polarity, falsifying it). Disjunction
  // packages take version 0 when the left disjunct is satisfied; negated
  // atoms contribute their conflict package at version 1.
  function PfWitness(r: set<Package>, f: PFormula, neg: bool): set<Package>
    decreases FSize(f)
  {
    match f
    case PAtom(n, vs) =>
      if !neg then {} else {Package(NegName(n, vs), 1)}
    case PAnd(a, b) =>
      if !neg then PfWitness(r, a, false) + PfWitness(r, b, false)
      else
        var orn := OrName(PNot(a), PNot(b));
        if !PfSat(r, a) then {Package(orn, 0)} + PfWitness(r, a, true)
        else {Package(orn, 1)} + PfWitness(r, b, true)
    case POr(a, b) =>
      if !neg then
        var orn := OrName(a, b);
        if PfSat(r, a) then {Package(orn, 0)} + PfWitness(r, a, false)
        else {Package(orn, 1)} + PfWitness(r, b, false)
      else PfWitness(r, a, true) + PfWitness(r, b, true)
    case PNot(g) => PfWitness(r, g, !neg)
  }

  // Conflict packages forced to version 0 by selected packages: whenever a
  // negated atom's conflicting package is in the resolution, the global
  // push edges of Definition 4.5.4(b)(vi) demand its kappa at 0.
  function PfPushNegs(r: set<Package>, pfdeps: PfDepRel): set<Package> {
    set e, q | e in pfdeps && q in EncAuxRepo(e.1, false) && q.name.NegName?
      && (exists u :: u in q.name.nscope && Package(q.name.nbase, u) in r)
      :: Package(q.name, 0)
  }

  function PfWitnessPart(r: set<Package>, pfdeps: PfDepRel): set<Package> {
    set e, q | e in pfdeps && e.0 in r && q in PfWitness(r, e.1, false) :: q
  }

  // Theorem 4.5.6: R̂ = R ∪ ⋃ W(ψ) (∪ the pushed conflict packages).
  function PfBuildCore(r: set<Package>, pfdeps: PfDepRel): set<Package> {
    r + PfWitnessPart(r, pfdeps) + PfPushNegs(r, pfdeps)
  }
}
