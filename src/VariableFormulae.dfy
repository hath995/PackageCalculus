// VariableFormulae.dfy — The Variable Formula Package Calculus (§4.6).
//
// Definitions 4.6.1 and 4.6.2 of the paper: package formulae extended with
// comparisons over global variables (opam's os-distribution, APT's
// architecture) and package-local variables (opam's with-test, Python's
// dependency groups). A resolution is paired with a variable assignment α;
// satisfaction carries the dependency context, so local variables are
// resolved against the depender.
//
// Variable values are naturals (the paper requires a total order on W).
// The reduction back to the core (Definition 4.6.3) extends the package
// formula reduction of §4.5 with packages for variables; it is not
// mechanised here (see README.md), but the calculus itself is executable
// and exercised in tests/Extensions.dfy with opam's
//   depends: [ "foo" { os = "linux" } ]
// pattern, expressed as ¬(os = linux) ∨ (foo ∧ os = linux).

include "Core.dfy"

module VariableFormulae {
  import opened Core

  // Definition 4.6.1(a): values W (totally ordered), global variables G,
  // and local variables P × L; the assignment function α.
  type VarValue = nat

  datatype VarKey = GlobalVar(g: string) | LocalVar(owner: Package, l: string)

  type Assignment = map<VarKey, VarValue>

  datatype CmpOp = Ge | Gt | Le | Lt | Eq | Ne

  predicate CmpHolds(op: CmpOp, x: VarValue, w: VarValue) {
    match op
    case Ge => x >= w
    case Gt => x > w
    case Le => x <= w
    case Lt => x < w
    case Eq => x == w
    case Ne => x != w
  }

  // Definition 4.6.1(b): variable formulae.
  datatype VForm =
    | VfAtom(name: Name, versions: set<Version>)
    | VfAnd(left: VForm, right: VForm)
    | VfOr(left: VForm, right: VForm)
    | VfNot(f: VForm)
    | VfGlobal(gvar: string, op: CmpOp, w: VarValue)   // GCP rule
    | VfLocal(lvar: string, op: CmpOp, w: VarValue)    // LCP rule

  // Definition 4.6.1(c): variable formula dependencies.
  type VFormDepRel = set<(Package, VForm)>

  // Definition 4.6.1(d): (r, α) ⊨_δ(f). The DEP/AND/OR/NOT rules carry
  // over from Definition 4.5.1(b); GCP and LCP compare assigned values,
  // local variables belonging to the dependency's owner.
  predicate VSat(r: set<Package>, asg: Assignment, owner: Package, f: VForm) {
    match f
    case VfAtom(n, vs) => exists v :: v in vs && Package(n, v) in r
    case VfAnd(a, b) => VSat(r, asg, owner, a) && VSat(r, asg, owner, b)
    case VfOr(a, b) => VSat(r, asg, owner, a) || VSat(r, asg, owner, b)
    case VfNot(g) => !VSat(r, asg, owner, g)
    case VfGlobal(g, op, w) =>
      GlobalVar(g) in asg && CmpHolds(op, asg[GlobalVar(g)], w)
    case VfLocal(l, op, w) =>
      LocalVar(owner, l) in asg && CmpHolds(op, asg[LocalVar(owner, l)], w)
  }

  // Definition 4.6.2(b): formula closure under (r, α).
  predicate VFormClosure(vdeps: VFormDepRel, r: set<Package>, asg: Assignment) {
    forall e | e in vdeps && e.0 in r :: VSat(r, asg, e.0, e.1)
  }

  // Definition 4.6.2: (r, α) ∈ S_α(D_α, root).
  predicate ValidVarFormResolution(repo: set<Package>, vdeps: VFormDepRel,
                                   root: Package, r: set<Package>, asg: Assignment) {
    r <= repo
    && RootInclusion(root, r)
    && VFormClosure(vdeps, r, asg)
    && VersionUniqueness(r)
  }
}
