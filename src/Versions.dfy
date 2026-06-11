// Versions.dfy — Version orderings and the Version Formula Calculus (§3.2).
//
// Definitions 3.2.1–3.2.6 of the paper. The total ordering on versions
// (Definition 3.2.1) is the ordering on naturals, fixed in Core.Version.
// The theorems about these definitions (the resolution ordering is a
// partial order; Theorem 3.2.7, correctness of the reduction) are proved
// in lemmas/VersionsLemmas.dfy.

include "Core.dfy"

module Versions {
  import opened Core

  // Definition 3.2.1, lifted to packages: (n, v1) ≤ (n, v2) ⟺ v1 ≤ v2.
  predicate PkgLeq(p1: Package, p2: Package) {
    p1.name == p2.name && p1.version <= p2.version
  }

  // Definition 3.2.2 (Resolution Ordering): r1 ⊑ r2 iff every package in r2
  // has a counterpart of the same name in r1 with a lower-or-equal version.
  // Maximal elements are the `freshest' resolutions.
  predicate ResLeq(r1: set<Package>, r2: set<Package>) {
    forall p2 | p2 in r2 ::
      exists p1 :: p1 in r1 && p1.name == p2.name && p1.version <= p2.version
  }

  // Definition 3.2.3(c): version formulae.
  //   φ ::= ⊤ | φ ∧ φ | φ ∨ φ | ρ v      ρ ::= ≥ | > | ≤ | < | = | ≠
  datatype VOp = Ge | Gt | Le | Lt | VEq | VNe

  datatype VFormula =
    | Top
    | VAnd(left: VFormula, right: VFormula)
    | VOr(left: VFormula, right: VFormula)
    | VCmp(op: VOp, v: Version)

  predicate OpHolds(op: VOp, u: Version, v: Version)
    requires op.Ge? || op.Gt? || op.Le? || op.Lt?
  {
    match op
    case Ge => u >= v
    case Gt => u > v
    case Le => u <= v
    case Lt => u < v
  }

  // Definition 3.2.3(e): the semantics function ⟦φ⟧ ⊆ V, evaluated against
  // 𝒱_n, the versions of the dependee name that exist.
  function Eval(f: VFormula, universe: set<Version>): set<Version> {
    match f
    case Top => universe
    case VAnd(a, b) => Eval(a, universe) * Eval(b, universe)
    case VOr(a, b) => Eval(a, universe) + Eval(b, universe)
    case VCmp(op, v) =>
      match op
      case VEq => {v}
      case VNe => universe - {v}
      case _ => set u | u in universe && OpHolds(op, u, v)
  }

  // Definition 3.2.4: version formula dependencies D_φ ⊆ P × (N × Φ).
  datatype VfDep = VfDep(name: Name, formula: VFormula)
  type VfDepRel = set<(Package, VfDep)>

  // Definition 3.2.5(b): dependency closure under formula semantics.
  predicate VfDepClosure(repo: set<Package>, vdeps: VfDepRel, r: set<Package>) {
    forall e | e in vdeps && e.0 in r ::
      exists u :: u in Eval(e.1.formula, VersionsOf(repo, e.1.name))
               && Package(e.1.name, u) in r
  }

  // Definition 3.2.5: r ∈ S_φ(D_φ, root).
  predicate ValidVfResolution(repo: set<Package>, vdeps: VfDepRel, root: Package, r: set<Package>) {
    r <= repo
    && RootInclusion(root, r)
    && VfDepClosure(repo, vdeps, r)
    && VersionUniqueness(r)
  }

  // Definition 3.2.6 (Version Formula Reduction): evaluate each formula to
  // its version set. Packages are unchanged (R := R_φ, root := root_φ).
  function ReduceVf(repo: set<Package>, vdeps: VfDepRel): DepRel {
    set e | e in vdeps :: (e.0, Dep(e.1.name, Eval(e.1.formula, VersionsOf(repo, e.1.name))))
  }
}
