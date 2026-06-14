# Design notes: the Package Calculus and a package manager for Dafny

Notes from design discussions on applying this mechanisation. Two threads:
which of the paper's extensions a Dafny package manager should adopt, and a
proposal for contract-derived version numbering. See also FINDINGS.md and
README.md for what is formally verified in this repository.

## 1. Which calculus features fit a Dafny package manager?

Dafny is an unusually interesting fit for this calculus, because
verification changes which extensions matter.

### Where Dafny sits on the paper's spectrum (§3.3)

Dafny has the OCaml problem, but worse. In OCaml, any API change is
potentially breaking; in Dafny, even *proof-irrelevant-looking* changes
break downstream **verification** — a changed function body alters what
callers see through revealed definitions, triggers shift, resource limits
get exceeded. Semantic versioning can't honestly promise "minor =
compatible" when compatibility includes "your proofs still go through."
So:

- **MVS is out** (it relies on semver discipline Dafny can't have), and
  upper-bound-free constraints are risky.
- That pushes Dafny to the opam end: **version uniqueness, full version
  formulae (§3.2), NP-complete resolution, a curated registry with
  reverse-dependency re-verification** on new releases — opam's model,
  except the reverse-dependency check is `dafny verify`, which is a much
  stronger and more meaningful compatibility check than OCaml's
  type-level one.
- **Concurrent versions (§4.2) and peer deps (§4.3) are the extensions to
  skip.** Dafny's module namespace is flat per program and there is no
  name-mangling story for linking two versions of `Std` into one
  verification run. Cargo's trick doesn't transfer.

### Extensions that map surprisingly well

- **Virtual packages (§4.7) ≈ abstract modules.** Dafny has a
  language-level notion the other ecosystems fake: a package can depend on
  an *abstract module signature*, and any package providing a concrete
  refinement satisfies it. That is literally the provides relation —
  depend on `ordered-map-interface`, provided by `red-black-tree-pkg` or
  `avl-pkg`. Also the toolchain itself: a dependency on `smt-solver`
  provided by z3 or cvc5. Probably the highest-value "exotic" extension
  for Dafny.
- **Variable formulae (§4.6) for compilation targets and the toolchain.**
  A Dafny package compiles to C#, Java, Go, JS, Python — `:extern`
  dependencies are inherently target-conditional, opam's
  `os-distribution` pattern verbatim: `¬(target = java) ∨
  java-runtime-shim`. Global variables for `dafny-version` and
  `solver-version` matter more than in any mainstream ecosystem, because
  proofs are brittle against both — the toolchain version belongs *inside*
  resolution, not outside it. Local variables give `with-test` /
  `with-docs` dependency groups for free.
- **Features (§4.4) for trust levels.** A genuinely Dafny-specific use:
  feature flags like `axiom-free` or `assume-free` selecting the
  fully-verified subset of a library versus the portion that relies on
  `{:axiom}`/`:extern` trust. Feature unification has the right
  semantics — if anything in the closure demands the verified-only build
  of a dependency, everyone gets it.
- **Singular dependencies (§4.9) + the build graph (§4.8) for reproducible
  verification.** Lockfiles aren't just nice for Dafny, they're what makes
  a verification cache *sound*: "this module verified" is only meaningful
  relative to the exact text of every dependee and the exact toolchain. A
  lockfile is a singular-dependency instance (the embedding is proved
  here), and Nix-style verification-cache substitution — skip re-verifying
  dependencies whose (content hash, toolchain) pair is already
  certified — is the analogue of binary caching. The build graph is the
  verification order.
- **Conflicts (§4.1)**, modestly: two packages exporting the same
  top-level module name, or demanding incompatible global flags
  (`--unicode-char`, type-system mode), genuinely cannot coexist.

### The self-hosting punchline

A Dafny package manager should be written in Dafny — and this repository
is most of its verified core. The validity checker is compiled and
executable; the reductions are proven compilation passes, so the resolver
only ever needs to solve **core** instances; and Appendix C's SAT
encoding is verified (`EncodeSound`/`EncodeComplete`), with Dafny already
shipping Z3. The pipeline "parse manifest → lower extensions to core
(proven) → encode to SAT (proven) → ask the bundled Z3 → decode (proven)"
would make it the first package manager whose resolver is verified
end-to-end against its own semantics. The missing pieces are at the
edges: a manifest format, a registry, and a content-hashing scheme for
the verification cache.

## 2. Contract-derived version numbering

**Proposal.** Assign version numbers automatically from a compatibility
analysis between releases: additions only → fully compatible; a changed
function signature → incompatible; strengthened preconditions or weakened
postconditions → incompatible.

This is behavioral subtyping (Liskov substitution) applied to *releases* —
and Dafny is the one ecosystem where the idea closes, because the
compatibility judgment is itself a verification condition. "Is
`pre_old ⇒ pre_new`, and does `post_new ⇒ post_old` under `pre_old`?" are
formulas the verifier can discharge. Elm does this for *types* (the
compiler computes the semver bump); this is "Elm, but for contracts." The
variance directions are exactly right, and they have a useful converse: a
release that *weakens* preconditions or *strengthens* postconditions is
also fully compatible, not just additions.

### How it lands in the calculus

- **It rehabilitates the tractable end of §3.3 for Dafny.** Where
  "compatible" cannot be promised socially, this scheme replaces the
  social promise with a theorem. The paper's approach (1) — restrict
  constraints to minimum bounds, get linear-time MVS-style resolution —
  is *sound* exactly when versions above the bound really are
  substitutable, which Go assumes and this checker would prove. The
  granularity function `g` of §4.2 (already mechanised) is precisely the
  compatibility class: `g(v)` = number of proven-incompatible steps
  before v. Checking only against the immediate predecessor suffices,
  because the relation is transitive — implication chains compose — so
  one VC set per release certifies compatibility with the whole class.
- Since classes are machine-checked, distinct compatibility classes could
  safely be treated as distinct package names (Go's major-version trick),
  at which point the Concurrent calculus (§4.2, fully proved here)
  applies with `g` = class.

### What "compatible" must mean in Dafny, beyond the three rules

- **Transparent function bodies.** Dafny functions are revealed by
  default; callers' proofs can depend on the body, so a body change with
  identical contracts is still breaking — unless the checker proves
  extensional equality (`∀x · f_old(x) == f_new(x)`, another VC) or the
  ecosystem adopts opaque-plus-contract discipline, with `export` sets
  making the spec surface explicit.
- **Datatypes are nearly frozen within a class.** Adding a constructor
  breaks every exhaustive `match` and case-analysis lemma downstream.
  Additions are *not* always compatible — that also covers names
  colliding with clients' `import opened`.
- **Frames are contracts too.** A grown `reads`/`modifies` clause breaks
  callers' framing arguments; frames must shrink or stay equal, like
  preconditions.
- **Lemmas are specs.** Weakening a lemma's conclusion or strengthening
  its hypotheses is breaking by the same rule — lemmas are ghost methods.
- **The trust base needs its own gate.** A "compatible" release that adds
  an `{:axiom}`, `assume`, or `:extern` can make clients prove *more*
  than before — including, in the worst case, `false`. Pre/post variance
  doesn't see that; any growth of the unverified surface should be at
  least a major bump.

### Caveat

Spec-level compatibility guarantees clients remain *logically*
verifiable, not that their proofs *replay* — triggers shift, resource
limits get crossed. The guarantee is "no client is wrong now," not "no
client needs proof repair." Practically: pair auto-versioning with
lockfiles for CI (the §4.9 singular instance) while letting dev builds
float within a compatibility class. The conservative failure mode is
benign — when the verifier can't prove compatibility, bump major; never
unsound, occasionally over-cautious.

### Implementation sketch

Since the registry holds the predecessor, the checker downloads it, wraps
its sources in a module (no renaming of internals needed — module
references resolve lexically, while the shared standard library escapes
to the common vocabulary), and emits a file of compatibility obligations:
one `PreWeakened` lemma per changed `requires` (old-pre ⇒ new-pre), one
`PostStrengthened` lemma per changed `ensures` (old-pre ∧ new-post ⇒
old-post, with the result as a bound variable), one `BodyEquivalent`
lemma per rewritten transparent body. Signature changes fail to resolve —
automatic major; unchanged contracts are skipped; additions carry no
obligation. Bodies default to `{}`; obligations the solver cannot
discharge call an author-maintained `<Obligation>_Manual` lemma, so
inductive cases get human proofs without regeneration clobbering them.
`dafny verify` on the generated file *is* the bump decision, and the
registry re-verifies it on upload, making the compatibility claim an
auditable artifact.

### Follow-ups mechanised in this repo

- The payoff of the scheme — linear-time, lockfile-optional resolution
  over minimum bounds — is the §3.3 material mechanised in
  `src/MinVersion.dfy` / `lemmas/MinVersionLemmas.dfy`; see README.md and
  FINDINGS.md for what is proved and which informal claims needed
  qualification.
- The implementation sketch above is pinned down by a worked example in
  `compat/`: a three-release library (`SeqLibV1..V3`), the generated
  obligations for a compatible pair (`CompatV1V2.dfy`, including a
  redefined recursive predicate discharged through the manual-proof hook
  in `CompatProofs.dfy`) and for a breaking pair (`CompatV2V3.dfy`, with
  the failing obligations refuted by verified witnesses and executable
  tests).
