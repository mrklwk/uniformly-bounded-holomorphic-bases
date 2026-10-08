# Palomar local preparation

Palomar submission and registration have not occurred.
The statement package is implemented: `Challenge.lean` imports only Mathlib,
`Solution.lean` proves the corresponding `BourgainStatement.manuscript_main`,
and `comparator.json` selects that declaration with the three standard axioms.
Definitions and theorem statement are duplicated identically in independent
module environments. The Challenge has one deliberate theorem placeholder;
Solution and production proofs have none.

The active migration now pins Lean **4.35.0-rc2** and canonical mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The matching tools and cache are
already used in the recorded Linux verification environment.
No new software installation or security change is needed for project compilation
and direct exported-proof checks. The original 4.34.1 candidate is preserved.

The official sources checked on October 7, 2026 are
[policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
[toolchain minimum](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json),
[metadata v0.4](https://github.com/mathlib-initiative/formalization.yaml), and
[template comparator script](https://github.com/PalomarRegistry/PalomarTemplate/blob/main/scripts/verify-comparator.sh).

## Migration scope

The active pins agree with the retained migration inputs. The only Solution proof
edit removes a redundant tactic line in bar_eq; all production proof sources,
statement definitions and theorem statements are unchanged. The pinned mathlib
[toolchain file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/lean-toolchain)
confirms the matching compiler. Reproducible project-only checks use the script
in docs/VERIFICATION.md and already cached dependencies.

## Comparator and complete mechanical preflight

The public commit `2d23de9224f7f9436eaae70e4e1290cd39ef0592` passed sandboxed Comparator (exit 0) with Lean, NanoDa and con-ron. The installed off-PATH bubblewrap was selected through COMPARATOR_BWRAP; no security setting was changed. The full Palomar mechanical preflight is a separate requirement and remains pending.

The manual workflow `.github/workflows/palomar-preflight.yml` calls the complete
PalomarSubmission workflow at its pinned revision with mode full and profile
palomar-standard-v1. Submission requires a mechanical report with status pass
for the exact intended commit. Standalone Comparator is not that report.

For future official checking, keep `external_kernels` out of the submitted
comparator.json and follow the current trusted runner's configuration. The
read-only preflight script can diagnose installed prerequisites without
installing or changing them.

## Local release metadata

Mark Lewko is the confirmed human author and responsible maintainer. Original
project contributions are licensed under AGPL-3.0-only in LICENSE; NOTICE and
third_party/licenses preserve the distinct upstream licenses and attribution.
AI assistance and AI review remain disclosed separately; no human peer review
is claimed.

`formalization.yaml` is the release metadata in JSON (a valid YAML
subset). Its authorship and license fields are approved, not placeholders.
Historical Git identities and all frozen audit commits are preserved. Original
manuscript byte/PDF reconciliation and complete Palomar mechanical preflight
remain unresolved. Submission and registration have not occurred.

## Final local review boundary

The submission draft selects only the verified d≥2 theorem. The approved title
is retained verbatim; it does not enlarge the declaration’s `0 < m` hypothesis
or claim that the separate d=1 proposal has passed the release toolchain.
The separate d=1 proposal has not been integrated or checked on the release
toolchain.

The prepared [hosted validation workflow](HOSTED_VALIDATION.md) is manual-only.
It has not run and does not change the recorded Comparator status.
