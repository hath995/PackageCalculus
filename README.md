# The Package Calculus, in Dafny

A mechanisation of **"Package Managers à la Carte: A Formal Model of
Dependency Resolution"** (Gibb, Ferris, Allsopp, Gazagnaire, Madhavapeddy;
arXiv:2602.18602v1, `2602.18602v1.pdf` in this directory).

The paper defines the *Package Calculus* — a minimal formal system for
dependency resolution (root inclusion, dependency closure, version
uniqueness) — and models the diversity of real-world package managers as
extensions with sound and complete reductions back to the core.

## Layout

```
dfyconfig.toml        Dafny project file (verifies/tests everything at once)
src/                  Definitions and executable functions/methods
  Core.dfy              §3.1  core calculus; Name/PFormula datatypes
  Solver.dfy            exhaustive resolver with a verified exactness contract
  Versions.dfy          §3.2  version/resolution orderings, Version Formula Calculus
  Conflicts.dfy         §4.1  Conflict Package Calculus + reduction
  Concurrent.dfy        §4.2  Concurrent Package Calculus + reduction
  Peers.dfy             §4.3  Peer Package Calculus + reduction
  Features.dfy          §4.4  Feature Package Calculus + reduction
  PackageFormulae.dfy   §4.5  Package Formula Calculus + Tseitin reduction
  VariableFormulae.dfy  §4.6  Variable Formula Calculus
  Virtual.dfy           §4.7  Virtual Package Calculus + reduction
  Optional.dfy          §4.8  build graphs and optional dependencies
  Singular.dfy          §4.9  singular (exact-version) dependencies
  SatEncoding.dfy       App C SAT encoding of resolution
  Hardness.dfy          App B 3-SAT → resolution construction
lemmas/               Proofs of the paper's claims (all machine-checked)
tests/                Executable examples from the paper (`dafny test`)
```

All predicates in `src/` are compiled (non-ghost), so a candidate
resolution can be *checked* mechanically — that executability is the
NP-membership half of Theorem 3.1.4.

## Paper claim → Dafny lemma

| Paper | Claim | Lemma (all verified, no assumes/axioms) |
|---|---|---|
| Def 3.2.2 | resolution ordering is a partial order on S(D, r) | `ResLeqRefl`, `ResLeqTrans`, `ResLeqAntisym` (VersionsLemmas) |
| Thm 3.2.7 | version formula reduction is correct | `VfReductionCorrect` (VersionsLemmas) |
| Thm 3.1.4 | NP-hardness via 3-SAT (Appendix B) | `SatGivesResolution`, `ResolutionGivesSat`, `HardnessCorrect` (HardnessLemmas) |
| Thm 3.1.4 | NP membership: poly-time checkable | `ValidResolution` is executable; `AllResolutions` (Solver.dfy) has a proven exactness contract |
| Thm 4.1.4/4.1.5 | conflict reduction sound & complete | `ConflictReductionSound`, `ConflictReductionComplete` (ConflictsLemmas) |
| Thm 4.2.4/4.2.5 | concurrent versions reduction sound & complete | `ConcReductionSound`, `ConcReductionComplete` (ConcurrentLemmas) |
| Def 4.2.1 | g = constant emulates the single-version core | `CoreEmulationForward`, `CoreEmulationBackward` (ConcurrentLemmas) |
| Thm 4.3.4/4.3.5 | peer dependency reduction sound & complete | `PeerReductionSound`, `PeerReductionComplete` (PeersLemmas) |
| Thm 4.4.5/4.4.6 | feature reduction sound & complete | `FeatReductionSound`, `FeatReductionComplete` (FeaturesLemmas) |
| §4.5 | package formulae subsume the core | `CoreEmbedding` (PackageFormulaeLemmas) |
| Thm 4.7.4/4.7.5 | virtual package reduction sound & complete | `VirtReductionSound`, `VirtReductionComplete` (VirtualLemmas) |
| §4.8 | optional deps affect only the build graph | `OptionalIrrelevantToResolution`, `BuildGraphMonotone`, `OptionalEdgeAlwaysPresent` (OptionalLemmas) |
| §4.9 | singular deps embed into the core (restriction) | `SingularEmbedding` (SingularLemmas) |
| Thm C.2/C.3 | SAT encoding sound & complete | `EncodeSound`, `EncodeComplete` (SatEncodingLemmas) |

The Tseitin-style package formula reduction (Definition 4.5.4) is
implemented (`EncTargets`/`EncAuxEdges`/`EncAuxRepo`) and validated
*exhaustively on the paper's Figure D.1 instance* — the resolver enumerates
the reduced instance's resolutions and they project onto exactly the
formula calculus's resolutions — but the general Theorems 4.5.5/4.5.6 are
not mechanised. Likewise §4.6's calculus is implemented and tested while
its reduction (Definition 4.6.3) and the §5.2 composition theorems are not.

## Modelling choices

- **Versions** are naturals (`type Version = nat`), supplying the total
  order of Definition 3.2.1. Where the paper's reductions need structured
  versions — the virtual package reduction encodes the chosen *provider*
  as the intermediate's version (Figure D.2) — the reduction takes an
  injective `enc : Package → Version` as a parameter.
- **Synthetic names** introduced by reductions (conflict κ-packages,
  granular names ⟨n, γ⟩, intermediates ⟨n, v, m⟩, feature packages ⟨n, f⟩,
  provider intermediates ⟨p, m⟩, Tseitin disjunction/negation packages)
  are constructors of the `Name` datatype; constructor injectivity and
  disjointness give the freshness properties the paper's reductions
  assume implicitly.
- **Intermediate naming** in §4.2/§4.3/§4.7 keys intermediates by
  (depender, dependee name), exactly as the paper's ⟨n, v, m⟩ — which
  presumes at most one dependency per (depender, name) pair. We surface
  that as the explicit `UniqueDepPerName` precondition (without it the
  paper's parent-relation theorems are not provable as stated). Similarly,
  `NonemptyDeps` excludes empty version sets, which the reductions would
  silently drop.
- **Parent/provider relations:** the §4.3 peer formalisation reuses the
  concurrent parent relation ρ ⊆ P × P (child, parent). The §4.7 provider
  relation is keyed by the dependency — π ⊆ (P × N) × P — so "exactly one
  provider" is expressible per dependency; with the paper's π ⊆ P × P, a
  provider selected for one dependency can alias another's.
- The version-formula semantics follows Definition 3.2.3(e) literally,
  including ⟦= v⟧ = {v} (not intersected with the existing versions).
- `ValidResolution` includes `r ⊆ repo` (resolutions are drawn from the
  packages that exist).

## Scope (what is not mechanised)

Theorems 4.5.5/4.5.6 (general Tseitin soundness/completeness — checked
exhaustively on Figure D.1 instead), Definition 4.6.3 and Theorems
4.6.4/4.6.5 (variable formula reduction), §5.2's composition theorems
(5.2.2/5.2.3), the §3.3 MVS/greedy complexity results, and Definition C.5
(ordered SAT). The §4.9 claim that the core *cannot* be reduced to
singular dependencies is an impossibility statement over all reductions
and is likewise out of scope. Nothing is assumed: there are no `axiom`s or
`assume` statements; every stated lemma is proved.

## Build & run

Requires Dafny ≥ 4.10.

```powershell
dafny verify dfyconfig.toml   # verify everything (105 obligations)
dafny test dfyconfig.toml     # verify + run the 18 example tests
```

Individual files can also be verified directly, e.g.
`dafny verify lemmas/ConcurrentLemmas.dfy`.
