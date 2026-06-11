# Finding: Theorem 5.2.2 of "Package Managers à la Carte" fails as stated

**Paper:** Package Managers à la Carte: A Formal Model of Dependency
Resolution (Gibb, Ferris, Allsopp, Gazagnaire, Madhavapeddy;
arXiv:2602.18602v1).

**Claim affected:** Theorem 5.2.2 (Soundness of the feature ∘ concurrent
composition): *if R is a valid core resolution of the doubly-reduced
instance, then the constructions of Theorems 4.2.4 and 4.4.5 yield a valid
resolution of the Concurrent Feature Package Calculus (Definition 5.2.1).*

**Status here:** refuted by an executable counterexample
(`tests/Composition.dfy`, `TestFeatureDrift`); a repaired version is
machine-checked (`lemmas/ConcurrentFeaturesLemmas.dfy`,
`ConcFeatReductionSoundCoherent`). The companion completeness direction,
Theorem 5.2.3, holds and is machine-checked (`ConcFeatComplete`).

## The gap

Section 5.2.1 argues the feature reduction (Definition 4.4.4) composes
with the concurrent versions reduction (Definition 4.2.3) "with no
modifications" because the feature reduction is **version-preserving**:
every synthetic feature package ⟨n, f⟩ inherits its base package's
version, so the granularity structure passes through unchanged.

That observation is true but insufficient. The feature reduction encodes a
dependency requiring features F = {f1, …, fk} as *k separate edges*

```
p → (⟨m, f1⟩, S),  …,  p → (⟨m, fk⟩, S)
```

and relies on the base edges ⟨m, fi⟩@v → (m, {v}) **plus core version
uniqueness** to force all k selections onto a single version of m — that
is how the reduction implements *feature unification* (Definition
4.4.3(d)/(b)). Version granularity (Definition 4.2.2(c)) deliberately
relaxes version uniqueness: distinct versions of m may coexist when their
granularities differ. The composed reduction therefore admits resolutions
in which the k feature edges of *one* dependency select *different*
versions of m at different granularities — call this **feature drift** —
and each carries only part of the required feature set.

## The counterexample

Versions encode semver as major·100; granularity is Cargo's
g(v) = v / 100.

- Repository: a@1.0.0, d@1.0.0, d@2.0.0; d supports f1 and f2 at both
  versions.
- One parameterised dependency: a → (d, {1.0.0, 2.0.0}, {f1, f2}).

After both reductions, the following set is a **valid core resolution**
(checked executably): a's f1-edge goes through its intermediate at
granularity 1 to ⟨⟨d,f1⟩,1⟩@1.0.0, while the f2-edge goes through its own
intermediate at granularity 2 to ⟨⟨d,f2⟩,2⟩@2.0.0; the base edges then pull
in ⟨d,1⟩@1.0.0 *and* ⟨d,2⟩@2.0.0 — legal, since the granularized names
differ.

Extracting per Theorem 4.2.4 gives a valid concurrent resolution of the
feature-reduced instance (that step is sound — machine-checked as
`ConcReductionSound`). Extracting per Theorem 4.4.5 then yields the
feature-level entries

```
(d@1.0.0, {f1})    (d@2.0.0, {f2})
```

— no selected version of d carries **both** f1 and f2, so Definition
5.2.1's closure for a's dependency is unsatisfiable by any choice of
witnesses. The extraction is not in S_γF: Theorem 5.2.2 fails.

Note the *instance* is satisfiable in the Concurrent Feature calculus
(select d@1.0.0 with {f1, f2}); what fails is the theorem's universal
quantification over core resolutions of the reduced instance. Soundness of
a reduction must hold for every solver answer, and a solver for the
reduced instance is free to return the drifted resolution.

Cargo itself does not exhibit this because a Cargo dependency is a single
edge carrying its feature set, unified per selected version by the
resolver; the drift is an artifact of the paper's per-feature edge
encoding surviving only as long as version uniqueness re-merges the edges.

## The repair (machine-checked)

Define **feature coherence** of a concurrent resolution (R_γ, ρ) of the
feature-reduced instance: for every dependency occurrence and every two
required features, the ρ-selected versions of the corresponding feature
edges coincide (`FeatureCoherent` in `src/ConcurrentFeatures.dfy`). This
is precisely the property version uniqueness used to provide for free.

- **Repaired Theorem 5.2.2** (`ConcFeatReductionSoundCoherent`): if R is a
  valid core resolution of the doubly-reduced instance and its Theorem
  4.2.4 extraction is feature-coherent, then the composed extraction —
  with selection witnesses read off ρ (`CFExtractSelP`/`CFExtractSelA`) —
  is a valid Concurrent Feature resolution. Fully verified.
- **Corollary** (`CoherentWhenSingleFeature`): coherence is automatic when
  no dependency requires more than one feature, so soundness holds
  unconditionally for that syntactic class. (With a constant granularity
  function, granularity collapses to uniqueness and the original §4.4
  theorems apply; that case is covered by `FeatReductionSound`.)
- **Theorem 5.2.3** (completeness) needs no hypothesis and is verified
  (`ConcFeatComplete`): resolutions constructed *from* the Concurrent
  Feature calculus never drift, because the construction places all of a
  dependency's feature packages at the single selected version.

An alternative repair, not pursued here, is to change the reduction: route
all of a dependency's feature edges through a shared per-dependency
intermediate (as the §4.3 peer reduction does with full-version
intermediates), making drift unrepresentable in the reduced instance. That
keeps the theorem hypothesis-free at the cost of a reduction that is aware
of the concurrent extension — consistent with the paper's own observation
(§5.2.2, "Limits of Composition") that some reductions must be made aware
of each other.

## Where to look

| Artifact | Location |
|---|---|
| Definition 5.2.1 (mechanised) | `src/ConcurrentFeatures.dfy` |
| Counterexample (executable) | `tests/Composition.dfy`, `TestFeatureDrift` |
| Feature coherence | `FeatureCoherent`, `src/ConcurrentFeatures.dfy` |
| Repaired soundness | `ConcFeatExtractSound`, `ConcFeatReductionSoundCoherent` |
| Single-feature corollary | `CoherentWhenSingleFeature` |
| Completeness (Thm 5.2.3) | `ConcFeatComplete` |
| Round-trip demo | `tests/Composition.dfy`, `TestConcFeatFigure9` |

One caveat: Definition 5.2.1 was reconstructed from a lossy text
extraction of the paper's PDF (mathematical symbols do not survive
`pdftotext`), so our reading — parent closure requiring a *single*
selected version carrying *all* required features, alongside the carried-
over Definitions 4.4.3(a)–(d) — could differ from the authors' intent.
The counterexample, however, violates the carried-over Definition
4.4.3(b) (parameterised dependency closure) directly, which any
reasonable reading retains.
