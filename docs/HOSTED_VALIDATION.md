# Prepared hosted validation — not executed

The manually dispatched `.github/workflows/validate.yml` adapts the official
[Palomar template CI](https://github.com/PalomarRegistry/PalomarTemplate/blob/main/.github/workflows/ci.yml)
and [Comparator script](https://github.com/PalomarRegistry/PalomarTemplate/blob/main/scripts/verify-comparator.sh),
reviewed October 7, 2026. Checkout, Lean action and artifact upload use the exact
40-character action pins from that workflow. Lean and mathlib remain pinned by
the project files. No runtime template-main fetch is used.

The metadata check verifies the exact approved AGPL-3.0 license bytes and
AGPL-3.0-only metadata, replacing the template's Apache-only check. This is an
exact-text check, not a new licensee detection run. It also checks dependency
pins and retained upstream license hashes. The workflow is JSON-formatted YAML.

Dispatch against the intended publication commit. It uses a disposable GitHub-hosted Ubuntu 24.04 runner,
installs the selected Lean environment through the pinned action, installs
bubblewrap and changes that runner's AppArmor user-namespace setting, as in
the official template. These operations have only been prepared, not executed.
No self-hosted runner is used. Push alone does not trigger execution.

The workflow builds all four project libraries, then invokes sandboxed
`lake comparator` with bundled NanoDa and con-ron in a temporary configuration.
The submitted comparator.json remains unchanged. There is no unsandboxed
fallback. Build and Comparator logs are uploaded as a workflow artifact.
A successful run must be tied to its exact Git commit before updating claims.
GitHub validation does not itself register a result with Palomar.

Local checks are structural and exact-hash checks, not official acceptance.
Full upstream JSON Schema validation and actionlint are not installed locally;
no tooling was installed to supply them. Official hosted validation remains pending.

Optional Lean-action GitHub caching, automatic tests and linting are disabled;
Mathlib's pinned cache is retained. The action's bundled tagged cache actions
therefore do not execute. Adapted template portions retain Apache-2.0 terms
and attribution in NOTICE and third_party/PalomarTemplate-LICENSE.
