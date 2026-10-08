# Licensing scope

Original contributions to this project are licensed under the GNU Affero General
Public License, version 3 only (`AGPL-3.0-only`), as authorized by Mark Lewko.
The full unmodified license text is in LICENSE. This grant covers the project's
original source, scripts and documentation; it does not relicense upstream
contributions, dependency repositories, their license texts, or cited papers.

Mark Lewko is the human author and responsible maintainer. This is a local
release: license and attribution do not imply
submission or registration action. Existing audited commits remain unchanged.

## Upstream material and compatibility check

The nine repositories pinned in lake-manifest.json declare Apache-2.0
(mathlib, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq,
batteries) or MIT (Cli). Their recorded license-file hashes at those exact
revisions match the unmodified local texts preserved in third_party/licenses.
The inventory records each revision, upstream URL, license and text hash.
No upstream implementation files, compiled libraries or tool binaries are
vendored in this source draft; only license texts are retained here as notices.
Lean and imported library contributions retain their upstream copyright and
attribution notices. Cited mathematical sources are not relicensed or redistributed.

No licensing conflict was identified for this source-only arrangement with
AGPL-3.0-only on original contributions and retained upstream permissions.
The Apache Software Foundation documents Apache-2.0's compatibility with GPLv3,
and the Free Software Foundation's GPLv3 guide explains both that compatibility
and combination with AGPLv3. Apache section 4 permits additional terms for
modifications while requiring retention of applicable upstream licenses and
notices. MIT permits reuse subject to keeping its copyright and permission notice.
This check covers the declared licenses of the pinned repositories and the
material in this draft, not a claim to relicense all upstream code or every
possible future binary distribution.

References: [Apache compatibility](https://apache.org/licenses/GPL-compatibility.html),
[FSF GPLv3 compatibility guide](https://www.gnu.org/licenses/quick-guide-gplv3.html),
[Apache-2.0 section 4](https://www.apache.org/licenses/LICENSE-2.0),
and [MIT terms](https://opensource.org/license/mit).

Keep upstream per-file copyright/license headers and any applicable NOTICE files
with upstream material if it is later copied or redistributed. The retained
license texts and NOTICE are attribution records, not an AGPL grant over
others' contributions. AI-assistance credits remain in CREDITS.md.
