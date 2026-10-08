# Reproducible local verification

The active project pins Lean 4.35.0-rc2 and mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Supply the matching already installed
compiler and existing pinned dependency cache:

```sh
python3 scripts/verify.py \
  --lean /path/to/lean-4.35.0-rc2/bin/lean \
  --packages /path/to/existing/.lake/packages \
  --output /path/outside/repository/new-verification-run
```

This is a **project-only fresh build using cached mathlib and other dependencies**.
It verifies dependency Git revisions and tracked cleanliness, rejects a nonempty
project object tree, builds every project source into external objects and records
commands, timings, exit statuses and source hashes. It neither installs software
nor downloads dependencies. The cached dependency object files are not rebuilt.

All proof and verification modules compile with warnings fatal. `Challenge.lean`
is the sole exception: it must emit exactly one deliberate theorem-placeholder
warning and no other warning. Solution does not import Challenge. The script also
requires 364 production axiom reports using only `propext`, `Classical.choice`
and `Quot.sound`. Unexpected axioms or failed commands stop the run.

The repository now ships both formerly private checks, without private context:

- `Verification/Semantics.lean`: twelve consequences checking the exact contract,
  actual formula, holomorphicity, nondegenerate sphere measure, L² membership,
  integrability, coefficient recovery and linear independence. All twelve have
  axiom reports. No production module imports this file.
- `Verification/Closure.lean`: walks types and values from the production theorem
  and the independent Solution theorem, rejects missing/unsafe/partial declarations
  and nonstandard axioms, and replays the union of their logical closures into an
  empty Lean kernel environment. It checks that coupled cancellation occurs and
  the unproved general-SPD proposition does not. It uses the installed Lean kernel,
  not an independently implemented checker. The traversal utility itself is a
  partial meta-program; partial constants in the logical closure are rejected.
  The harness explicitly imports the complete transitive private proof data;
  ordinary module interfaces alone are insufficient for a complete traversal.
  Its scope and axiom guards reject an incomplete interface-only traversal.

The script runs both checks automatically. It writes the closure list to the
external output path through `BOURGAIN_AUDIT_OUTPUT`; without that variable the
harness prints its results without writing a dependency file.

`Challenge.lean` expresses the full explicit construction with its own exponent
subtype and imports only Mathlib. `Solution.lean` independently repeats the same
statement definitions, proves their equality with the production construction,
and supplies `BourgainStatement.manuscript_main`. The adapted restatement originated
in Claude’s review; that earlier review does not certify later edits.
`scripts/check_layout.py` checks literal statement/definition agreement, import
boundaries, placeholder isolation and packaging. This source-level check is not
Comparator: the official comparison and independent NanoDa check remain pending.

Once matching dependencies are already provisioned, the ordinary Lake entry is
`lake build BourgainBasis Challenge Solution Verification`. The explicit offline
compiler driver is the tested build route; no successful `lake build`, dependency
rebuild, sandboxed Comparator run is implied. Direct exported-proof kernel checks are
reported separately from the project-only compilation and replay.

The original module-system candidate at `8eb23d7` passed 63 modules, twelve semantic
checks and a 53,547-declaration main closure replay; Claude independently repeated
those checks. The current follow-up adds Challenge, Solution and two shipped
verification modules. See the local verification receipt for its exact source
hashes and closure counts. Counts are snapshot-specific; PROVENANCE.md explains
the earlier 53,549 to 53,547 change.

The historical 4.34.1 follow-up's shipped closure harness replayed both roots successfully:
53,547 declarations in the production main closure and 53,566 in the combined
production/Solution closure. Only the three standard axioms occur; no logical
dependency is missing, unsafe or partial. The extra 19 declarations belong to the
independent statement bridge. The full-run receipt records the compilation and
semantic checks separately.

## Direct installed-kernel validation

In an already provisioned matching Linux environment, put the installed toolchain
binaries on PATH and set LEAN_PATH from the successful verification output's
lean-path.txt. From the repository, export the independently stated theorem:

```sh
leanexport Solution -- BourgainStatement.manuscript_main > /external/output/solution.export.jsonl
leanchecker --from-export /external/output/solution.export.jsonl
con-ron /external/output/solution.export.jsonl
```

Run `nanoda_bin /external/output/nanoda.json`, where the configuration contains
`use_stdin: false`, `export_file_path` set to that export,
`permitted_axioms: ["propext", "Classical.choice", "Quot.sound"]`,
`unpermitted_axiom_hard_error: true`, `num_threads: 4`, `nat_extension: true`
and `string_extension: true`. Record exact binary/export hashes and all exit
codes. These direct checks do not compare the Challenge under an official
sandbox and must not be called sandboxed Comparator acceptance.

## Completed 4.35.0-rc2 results

The supported-toolchain migration passed all 67 project modules, all twelve
semantic consequences, 364 production axiom reports and both theorem-root
checks. The production main closure has 53,753 declarations; the two-root union
has 53,772, replayed from an empty Lean kernel environment. Only the three
standard axioms occur, with no missing, unsafe or partial logical dependencies.
These counts differ from the historical 4.34.1 counts because the toolchain and
mathlib snapshot changed.

The independent Challenge and Solution have byte-identical complete elaborated
types. The exported Solution passed Lean checker, NanoDa and con-ron; con-ron
accepted 52,449 exported declarations. This exported closure is a different
representation from the in-process two-root replay. The 356,286,889-byte export
has SHA-256
`84237ceda0a19771b60eebd04de339cb9f656fc5c0cdee4122765cdc8b611ef2`.
The normal official Comparator invocation failed to start with exit 2 because
`bwrap` is missing. Direct independent-kernel success is not that receipt.
