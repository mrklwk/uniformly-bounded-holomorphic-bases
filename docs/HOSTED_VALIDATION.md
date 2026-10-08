# Full Palomar mechanical preflight

The manual `.github/workflows/palomar-preflight.yml` calls
PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml at
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, with the same pipeline_commit,
mode full and execution_profile palomar-standard-v1. It binds source to
`${{ github.sha }}`, uses project-root comparator.json and formalization.yaml,
and grants contents: read. No secrets are inherited.

The pinned upstream pipeline provisions its disposable runner and performs the
complete mechanical verification. Inspect its mechanical-report artifact and
require status pass for the exact intended submission commit. A successful
standalone Comparator run is not a substitute. This workflow does not perform
Palomar intake, editorial review or permanent registration.

The earlier standalone validation helper is superseded by this workflow for
Palomar readiness. It is not necessary to upload .github/workflows/validate.yml.
