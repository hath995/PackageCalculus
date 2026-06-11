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
include "PackageFormulae.dfy"

module VariableFormulae {
  import opened Core
  import opened PackageFormulae

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

  // ---------------------------------------------------------------------
  // The reduction to the core (Definition 4.6.3).
  //
  // Variable comparisons compile to package formula atoms over synthetic
  // *variable packages* — one package name per variable, whose versions
  // are the variable's existing values (the 𝒲 of Definition 4.6.1(a)) —
  // and the result is reduced by the package formula reduction of §4.5.
  // The paper encodes negated comparisons with complement operators; we
  // keep PNot and let §4.5's conflict encoding handle it, which matches
  // the satisfaction semantics above (a comparison on an unassigned
  // variable is false, so its negation holds).
  // ---------------------------------------------------------------------

  // The values of each variable that exist.
  type VarUniverse = set<(VarKey, VarValue)>

  function VKeyName(k: VarKey): Name {
    match k
    case GlobalVar(g) => GlobalVarName(g)
    case LocalVar(p, l) => LocalVarName(p, l)
  }

  function KeyOf(n: Name): VarKey
    requires n.GlobalVarName? || n.LocalVarName?
  {
    if n.GlobalVarName? then GlobalVar(n.gname) else LocalVar(n.lowner, n.lname)
  }

  // ⟦ρ w⟧ against the variable's existing values.
  function CmpVals(univ: VarUniverse, k: VarKey, op: CmpOp, w: VarValue): set<VarValue> {
    set e | e in univ && e.0 == k && CmpHolds(op, e.1, w) :: e.1
  }

  // Definition 4.6.3(b), as a compilation into the §4.5 formula language.
  function Compile(f: VForm, owner: Package, univ: VarUniverse): PFormula {
    match f
    case VfAtom(n, vs) => PAtom(n, vs)
    case VfAnd(a, b) => PAnd(Compile(a, owner, univ), Compile(b, owner, univ))
    case VfOr(a, b) => POr(Compile(a, owner, univ), Compile(b, owner, univ))
    case VfNot(g) => PNot(Compile(g, owner, univ))
    case VfGlobal(g, op, w) =>
      PAtom(GlobalVarName(g), CmpVals(univ, GlobalVar(g), op, w))
    case VfLocal(l, op, w) =>
      PAtom(LocalVarName(owner, l), CmpVals(univ, LocalVar(owner, l), op, w))
  }

  function CompileDeps(vdeps: VFormDepRel, univ: VarUniverse): PfDepRel {
    set e | e in vdeps :: (e.0, Compile(e.1, e.0, univ))
  }

  // Definition 4.6.3(a)(i)/(ii): the variable packages.
  function VarPkgsUniverse(univ: VarUniverse): set<Package> {
    set e | e in univ :: Package(VKeyName(e.0), e.1)
  }

  // An assignment as a set of selected variable packages, and back.
  function AsgPkgs(asg: Assignment): set<Package> {
    set k | k in asg :: Package(VKeyName(k), asg[k])
  }

  function AsgOf(r: set<Package>): Assignment
    requires VersionUniqueness(r)
  {
    map p | p in r && (p.name.GlobalVarName? || p.name.LocalVarName?) ::
      KeyOf(p.name) := p.version
  }

  // Freshness and well-formedness for the reduction.
  predicate PlainVForm(f: VForm) {
    match f
    case VfAtom(n, _) =>
      !n.OrName? && !n.NegName? && !n.GlobalVarName? && !n.LocalVarName?
    case VfAnd(a, b) => PlainVForm(a) && PlainVForm(b)
    case VfOr(a, b) => PlainVForm(a) && PlainVForm(b)
    case VfNot(g) => PlainVForm(g)
    case VfGlobal(_, _, _) => true
    case VfLocal(_, _, _) => true
  }

  predicate PlainVarInstance(repo: set<Package>, vdeps: VFormDepRel) {
    (forall p | p in repo ::
       !p.name.OrName? && !p.name.NegName?
       && !p.name.GlobalVarName? && !p.name.LocalVarName?)
    && (forall e | e in vdeps :: e.0 in repo && PlainVForm(e.1))
  }

  // The assignment respects the value universe.
  predicate AsgInUniverse(asg: Assignment, univ: VarUniverse) {
    forall k | k in asg :: (k, asg[k]) in univ
  }

  // Definition 4.6.3: the composed reduction — add the variable packages
  // to the repository, compile the formulae, and apply the §4.5 reduction.
  function VarReduceRepo(repo: set<Package>, vdeps: VFormDepRel, univ: VarUniverse): set<Package> {
    PfReduceRepo(repo + VarPkgsUniverse(univ), CompileDeps(vdeps, univ))
  }

  function VarReduceDeps(vdeps: VFormDepRel, univ: VarUniverse): DepRel {
    PfReduceDeps(CompileDeps(vdeps, univ))
  }

  // The constructions of Theorems 4.6.4 and 4.6.5: a variable-calculus
  // resolution pairs with its assignment's packages, and conversely the
  // assignment is read off the selected variable packages.
  function VarBuildPf(rv: set<Package>, asg: Assignment): set<Package> {
    rv + AsgPkgs(asg)
  }

  function VarBuildCore(rv: set<Package>, asg: Assignment,
                        vdeps: VFormDepRel, univ: VarUniverse): set<Package> {
    PfBuildCore(VarBuildPf(rv, asg), CompileDeps(vdeps, univ))
  }
}
