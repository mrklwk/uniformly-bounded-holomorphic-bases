# Credits and attribution

**Author and responsible maintainer:** Mark Lewko.

**Formalization process:** the Lean development was produced with OpenAI Codex
under the mathematical project owner's direction. Its use of agent-generated
proofs and separate agent review is disclosed in the draft metadata. The human author and responsible maintainer is Mark Lewko.
An AI tool is not placed in either field. Claude supplied a separate AI review
of candidate 8eb23d7 and an independent mathematical restatement, adapted here
for the Challenge/Solution interface. No person is credited with an independent human
review that has not occurred.

**Libraries:** Lean and mathlib provide the proof assistant and foundational
mathematics, including measure theory, finite-dimensional linear algebra,
Fourier characters, Stirling/Gamma estimates and real/complex analysis. The
exact dependency commits are recorded in `lake-manifest.json`.

**Mathematical background cited by the manuscript:**

- Jean Bourgain, *Applications of the spaces of homogeneous polynomials to some
  problems on the ball algebra*, Proc. Amer. Math. Soc. 93 (1985), 277–283.
  DOI: [10.1090/S0002-9939-1985-0770536-4](https://doi.org/10.1090/S0002-9939-1985-0770536-4).
- Jean Bourgain, *On uniformly bounded bases in spaces of holomorphic functions*,
  Amer. J. Math. 138 (2016), 571–584.
  DOI: [10.1353/ajm.2016.0018](https://doi.org/10.1353/ajm.2016.0018).
  The [June 2015 preprint](https://arxiv.org/abs/1506.05694) uses “basis”
  (singular) in its title; §3 attributes the question to W. Rudin.

Additional primary references and their precise scope are given in
[historical context](docs/HISTORY.md).

These are background citations from the manuscript, not unproved analytic
hypotheses imported into the final Lean theorem. No authorship of this
formalization is attributed to those authors.

Git packaging operations are credited to OpenAI Codex, separately from the
human authorship and maintainership recorded above.

Original project contributions are licensed under AGPL-3.0-only. Upstream
implementation contributions and license texts retain their own terms and
attributions, as recorded in NOTICE and third_party/licenses/inventory.json.
