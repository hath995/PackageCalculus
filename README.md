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
dfyconfig.toml          Dafny project file (verifies/tests everything at once)
src/                    Definitions and executable functions/methods
  Core.dfy                §3.1  core calculus; Name/PFormula datatypes
  Solver.dfy              exhaustive resolver with a verified exactness contract
  Versions.dfy            §3.2  version/resolution orderings, Version Formula Calculus
  Conflicts.dfy           §4.1  Conflict Package Calculus + reduction
  Concurrent.dfy          §4.2  Concurrent Package Calculus + reduction
  Peers.dfy               §4.3  Peer Package Calculus + reduction
  Features.dfy            §4.4  Feature Package Calculus + reduction
  PackageFormulae.dfy     §4.5  Package Formula Calculus + Tseitin reduction
  VariableFormulae.dfy    §4.6  Variable Formula Calculus + reduction (via §4.5)
  Virtual.dfy             §4.7  Virtual Package Calculus + reduction
  Optional.dfy            §4.8  build graphs and optional dependencies
  Singular.dfy            §4.9  singular (exact-version) dependencies
  ConcurrentFeatures.dfy  §5.2  Concurrent Feature Package Calculus + composed reduction
  SatEncoding.dfy         App C SAT encoding of resolution
  Hardness.dfy            App B 3-SAT → resolution construction
lemmas/                 Proofs of the paper's claims (all machine-checked)
tests/                  Executable examples from the paper (`dafny test`)
```

All predicates in `src/` are compiled (non-ghost), so a candidate
resolution can be *checked* mechanically — that executability is the
NP-membership half of Theorem 3.1.4.

## Paper claim → Dafny lemma

| Paper | Claim | Lemma (all verified; no assumes/axioms anywhere) |
|---|---|---|
| Def 3.2.2 | resolution ordering is a partial order on S(D, r) | `ResLeqRefl/Trans/Antisym` (VersionsLemmas) |
| Thm 3.2.7 | version formula reduction correct | `VfReductionCorrect` (VersionsLemmas) |
| Thm 3.1.4 | NP-hardness via 3-SAT (App. B) | `SatGivesResolution`, `ResolutionGivesSat`, `HardnessCorrect` (HardnessLemmas) |
| Thm 3.1.4 | NP membership | executable `ValidResolution`; `AllResolutions` exactness contract (Solver) |
| Thm 4.1.4/4.1.5 | conflict reduction sound & complete | `ConflictReduction{Sound,Complete}` (ConflictsLemmas) |
| Thm 4.2.4/4.2.5 | concurrent versions reduction sound & complete | `ConcReduction{Sound,Complete}` (ConcurrentLemmas) |
| Def 4.2.1 | constant g emulates the core | `CoreEmulation{Forward,Backward}` (ConcurrentLemmas) |
| Thm 4.3.4/4.3.5 | peer dependency reduction sound & complete | `PeerReduction{Sound,Complete}` (PeersLemmas) |
| Thm 4.4.5/4.4.6 | feature reduction sound & complete | `FeatReduction{Sound,Complete}` (FeaturesLemmas) |
| §4.5 | package formulae subsume the core | `CoreEmbedding` (PackageFormulaeLemmas) |
| Thm 4.5.5/4.5.6 | Tseitin formula reduction sound & complete | `PfReduction{Sound,Complete}` (TseitinLemmas) |
| Thm 4.6.4/4.6.5 | variable formula reduction sound & complete | `VarReduction{Sound,Complete}` (VariableFormulaeLemmas), via SatTransfer + the Tseitin theorems |
| Thm 4.7.4/4.7.5 | virtual package reduction sound & complete | `VirtReduction{Sound,Complete}` (VirtualLemmas) |
| §4.8 | optional deps affect only the build graph | `OptionalIrrelevantToResolution` etc. (OptionalLemmas) |
| §4.9 | singular deps embed into the core | `SingularEmbedding` (SingularLemmas) |
| Thm 5.2.3 | feature∘concurrent composition complete | `ConcFeatComplete` (ConcurrentFeaturesLemmas), via the bridge + Thm 4.2.5 |
| **Thm 5.2.2** | feature∘concurrent composition sound | **FALSE as stated** — see below and [FINDINGS.md](FINDINGS.md) |
| Thm 5.2.2′ | … sound under feature coherence | `ConcFeatReductionSoundCoherent` (ConcurrentFeaturesLemmas); `CoherentWhenSingleFeature` discharges the hypothesis when no dependency requires two features |
| Thm C.2/C.3 | SAT encoding sound & complete | `Encode{Sound,Complete}` (SatEncodingLemmas) |

## A finding: Theorem 5.2.2 fails as stated (and a verified repair)

The paper argues (§5.2.1) that the feature and concurrent-versions
reductions compose "with no modifications" because the feature reduction is
*version-preserving*. But the feature reduction achieves feature
**unification** through version **uniqueness** — the per-feature edges
`p → (⟨m,f⟩, S)` re-converge on one version of m only because the core
admits a single version per name. Version granularity (§4.2) deliberately
relaxes exactly that. A core resolution of the doubly-reduced instance can
therefore satisfy one dependency's required features `{f1, f2}` with *two*
versions of the dependee — `⟨d,f1⟩@1.0.0` and `⟨d,f2⟩@2.0.0` at different
majors ("feature drift") — and its extraction under Theorems 4.2.4 + 4.4.5
violates Definition 5.2.1's closure: no single selected version carries
both features. `tests/Composition.dfy: TestFeatureDrift` exhibits this
executably.

The repair is also mechanised: **feature coherence**
(`FeatureCoherent`) names the exact missing property — per dependency,
all required features select the same dependee version — and soundness is
proved under that hypothesis (`ConcFeatReductionSoundCoherent`), with a
corollary discharging it whenever no dependency requires more than one
feature (`CoherentWhenSingleFeature`). The drift counterexample is
precisely a failure of feature coherence (`expect !FeatureCoherent(...)`
in the test). The completeness direction (Theorem 5.2.3) needs no
hypothesis and is proved. Full discussion, including an alternative
reduction-level repair, in [FINDINGS.md](FINDINGS.md).

## Modelling choices

- **Versions** are naturals, supplying Definition 3.2.1's total order.
  Where a reduction needs structured versions (§4.7 encodes the chosen
  provider as the intermediate's version), it takes an injective
  `enc : Package → Version` parameter.
- **Synthetic names** (conflict κ-packages, granular ⟨n, γ⟩, intermediates
  ⟨n, v, m⟩, feature ⟨n, f⟩, provider ⟨p, m⟩, Tseitin disjunction/negation
  packages, variable packages) are constructors of `Name`; constructor
  injectivity and disjointness supply the freshness the paper assumes.
- **Implicit assumptions surfaced as preconditions:** the ⟨n, v, m⟩
  intermediate naming of §4.2/§4.3/§4.7 presumes at most one dependency
  per (depender, dependee-name) pair (`UniqueDepPerName`, and
  `CFUniqueDeps`/`CFUniqueAdds`/`CFAddNotSelf` for §5.2); empty version
  sets would vanish in the reductions (`NonemptyDeps`).
- **Witness relations:** the paper's parent/provider relations in P × P
  cannot express per-dependency uniqueness when selections alias; §4.7
  keys the provider relation by dependency, and §5.2 uses functional
  selection relations `selP`/`selA` keyed by dependency occurrence.
- §4.6 compiles variable comparisons to atoms over variable packages and
  reuses the §4.5 reduction; a comparison on an unassigned variable is
  false (so its negation holds), matching the satisfaction semantics.
- The version-formula semantics follows Definition 3.2.3(e) literally,
  including ⟦= v⟧ = {v}.

## Scope (what is not mechanised)

The §3.3 MVS/greedy complexity results, Definition C.5 (ordered SAT), and
the §4.9 impossibility remark (no reduction from the core to singular
dependencies — a statement over all reductions). Everything stated as a
lemma is proved; there are no `assume` statements or axioms.

## Build & run

Requires Dafny ≥ 4.10.

```powershell
dafny verify dfyconfig.toml   # verify everything
dafny test dfyconfig.toml     # verify + run the 21 example tests
```
