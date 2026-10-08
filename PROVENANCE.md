# Provenance

## Attribution

Mark Lewko is the human author and responsible maintainer. AI assistance and
review are described in CREDITS.md; no human peer review is claimed.

## Mathematical source

The mathematical source is nonpublic. The main theorem concerns every fixed d≥2
and every degree N≥0. Its displayed polynomial space is the span of the degree-N
monomials on ℂᵈ; its measure is normalized surface measure on the complex unit
sphere. The formal endpoint covers each homogeneous degree block, with a
dimension-dependent constant uniform in degree; it does not include a formal
Hardy-space completeness theorem. See docs/SCOPE.md.

Source comparison used authenticated text rather than a verified original-byte
download. Original
TeX byte identity and PDF reconciliation remain unresolved. No public manuscript
URL, DOI, or arXiv identifier is assigned here without verification. The manuscript
itself is not redistributed with this candidate.

## Formal source

The completed theorem implementation was frozen at
`86c77c95073edafea02fbd141f0f68722cd45b09`. The later author-evidence checkpoint
`851f8f2affc446b94078c056e35c83242f6e6751` has the same production Lean tree.
An independent agent audit rebuilt the original checkpoint and checked its
mathematical interpretation and complete final-theorem kernel dependency closure.
That is not a claim of human peer review or an independent implementation of Lean's
kernel.

This candidate exports that substantive development, rather than depending on a
separate unpublished proof repository. It adds Lean module headers, public
visibility and definition exposure for the module system, a package entry point,
portable build metadata, and documentation. The mathematical proofs and final
theorem are unchanged. The fresh candidate verification is distinct from the
review of the earlier snapshot.

## Fidelity

The explicit Fourier minors, increasing stars-and-bars convention, positive
Fourier sign, √2 quadratic phase, and m! monomial normalization are retained.
The full Poisson profile statement is proved by a discrete method. Only the
coupled quadratic matrix used by the main theorem is certified; the manuscript's
broader arbitrary-SPD proposition and continuous-Gamma appendix are outside the
formalization's proved scope. No such statement is an assumption of the main result.

The finite polynomial family is expressed through its Gram identity and exact
span. This gives an orthonormal basis in the intended L² space without requiring
a bundled `OrthonormalBasis` object as the exported statement.

## Independent AI review and follow-up

Claude reviewed local candidate `8eb23d7316bf3ed8eacb79f926d5b68a10a2a27d`.
The supplied review reports no mathematical gaps, a project-only fresh 63-module
build against cached mathlib, all 364 standard-axiom reports, successful semantic
and closure checks, and unchanged hashes for all 76 candidate files. Claude also
wrote an independent manuscript-form restatement. This is an AI review, not human
peer review or a Palomar decision. The review covers that frozen candidate, not
automatically the subsequent packaging additions.

The follow-up includes clean reproducible semantic and closure checks and adapts
Claude’s restatement into the Mathlib-only Challenge and proved Solution. Its
index type is now independently defined in both statement environments. The
original restatement and dialogue are not included in the proposed public tree.

The original proof snapshot’s main closure contained 53,549 declarations; the
module-system candidate’s contained 53,547. Comparing declaration lists after
removing generated module-private prefixes matches 101 renamed helpers and
leaves precisely `BourgainBasis.degreePermute._proof_5` and
`BourgainBasis.degreePermute._proof_6` in the original list only. These are generated
proof helpers, not extra mathematical premises. Counts describe their respective
compiled snapshots and are not an invariant proof-size metric. Both snapshots
were separately replayed; unchanged proof source alone was not used as a
substitute for that check.

## Supported-toolchain migration

A separate migration branch uses Lean 4.35.0-rc2 with canonical mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, reusing already installed tools and
cached dependencies from the recorded verification environment.
All production files under BourgainBasis are unchanged from the audited candidate.
The only Solution proof edit removes `ext k; simp` after `congr 2` in `bar_eq`,
because the newer tactic already closes that goal. Neither the theorem statements
nor definitions changed. The older 4.34.1 checkpoints remain preserved.

The migrated candidate was checked against the installed 4.35.0-rc2 compiler,
with fresh project objects and cached pinned dependencies. Complete elaborated
Challenge/Solution type equality and direct Lean/NanoDa/con-ron validation all
passed. The public commit `2d23de9224f7f9436eaae70e4e1290cd39ef0592` passed sandboxed Comparator (exit 0) with Lean, NanoDa and con-ron. The installed off-PATH bubblewrap was selected through COMPARATOR_BWRAP; no security setting was changed. The full Palomar mechanical preflight is a separate requirement and remains pending.

Primary historical attribution is recorded in [docs/HISTORY.md](docs/HISTORY.md).
