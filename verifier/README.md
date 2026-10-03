# Fast verification

The mathematical contract in `SigGolf/` is unchanged. The verifier has two transport modes,
explicit reverification controls, and a shared local/remote checker. No uploader attestation
is accepted, and no candidate-produced `.lake` tree becomes a trusted dependency cache.

## Modes and guarantees

| Mode | Candidate code execution | Authoritative artifact |
| --- | --- | --- |
| Source (no `submission/certificate/`) | Sandboxed build and export | Frozen admitted Lean source and its checked logical submission |
| Certificate | None | Frozen claim, four raw images, and kernel-checked declarative certificate |
| Certificate preview (`--preview`) | None | Development check only; no score or acceptance record |

Both official modes require supported unprivileged Linux, the existing systemd isolation,
and Landlock. Preview can run elsewhere, with wall/CPU/input/output limits but without the
official hard process-tree memory isolation. Preview never executes solver Lean source.

The checker uses the pinned comparator's exact theorem/definition-hole comparison, primitive
matching, permitted-axiom closure, and Lean kernel replay. Certificate mode additionally
selects `SigGolf.Challenge.image_binding`, an equality between the logical submission and
an organizer-generated literal submission containing the complete raw image bytes, sizes,
and layout. The literal is **not** a definition hole. Its definitions are recursively matched
against the trusted export. Hashes identify frozen files; they do not substitute for that proof.

Certificate-authoritative mode does not establish that supporting Lean source produced the
certificate. Source reproducibility is a separate audit requirement; use source mode if it is
required for acceptance. The protocol never silently falls back when an artifact is invalid.

## Preparing a certificate

Use a separate development project with the pinned dependencies, trusted `SigGolf/`, your
source modules, and a `lean_lib Solution` target. Do not add generated modules to the trusted
repository's `SigGolf/` or change project pins in a solver submission.

Place each program's instruction words in little-endian `PROGRAM.code` and its embedded bytes
in `PROGRAM.data`, for `keygen`, `sign`, `expand`, and `verify`. The producer may be untrusted:
the subsequent literal-equality proof is what establishes correspondence to the certified code.

```sh
python3 verifier/certificate.py prepare --source submission --images /path/to/images --project .work/dev
```

In that development project, build `Solution` and `SigGolf.CertifiedImages`, then compile the
generated equality module:

```sh
lake build Solution SigGolf.CertifiedImages
lake env lean -o .lake/build/lib/lean/CertificateBinding.olean CertificateBinding.lean
```

The default binding proof is `rfl`. If your representation needs a structural equality proof,
provide that proof in the development binding module; it must prove the **same** equality.

Export `CertificateBinding` with the five names in `verifier/comparator.json`,
`SigGolf.Challenge.image_binding`, `SigGolf.Challenge.submission`, the three permitted axioms,
and the primitive names listed in `verify.export_targets`. Use the pinned `lean4export`
executable, not a custom extractor. Its output is declarative, untrusted proof data.

```sh
python3 verifier/certificate.py pack --source submission --images /path/to/images \
  --export /path/to/binding.export --output submission/certificate
python3 scripts/run.py --fresh-kernel
```

For large certificates that cannot fit the archive, first produce the compressed proof outside
the bundle and identify a public GitHub release-asset URL:

```sh
python3 verifier/certificate.py pack --source submission --images /path/to/images \
  --export /path/to/binding.export --output submission/certificate \
  --proof-url https://github.com/OWNER/REPO/releases/download/TAG/proof.export.gz \
  --proof-output /path/to/proof.export.gz
```

Publish that exact generated file at the URL yourself; `pack` does not upload or create a release.
The anonymous supervisor fetches it only after a cache miss, validates its complete compressed
length and SHA-256, then validates the expanded bytes before kernel checking. Only public HTTPS
GitHub release assets and allowlisted GitHub asset redirects are accepted. No credentials,
cookies, or environment proxies are used. Download and expansion limits remain enforced.

`pack` refuses to overwrite an existing bundle. After source or claim changes, produce a new
bundle; the old manifest must not be relabeled. The local verifier freezes and identifies
all admitted source file paths and bytes, ignoring empty directories that Git cannot transport.
This identifies review material but is not producer provenance.

### Bundle format

`certificate/` contains exactly `manifest.json`, the eight raw image files, and `proof.export.gz`
for embedded mode. Detached mode omits the proof file and specifies `proof.url` instead of
`proof.file`. Manifest version 1 records the source digest, canonical claim, exact Lean toolchain,
each file's name/length/SHA-256, and the expanded proof's length/SHA-256. Duplicate JSON fields,
unknown files, symlinks, hardlinks, path traversal, and unsupported versions reject.

The original source limit remains 16 MiB and the total entry limit remains 1000. A bundle adds
at most 21 MiB: a compressed proof at most 16 MiB, a manifest at most 8 KiB, and four images
each strictly below 1 MiB. Expanded proof length and digest are checked while streaming.
Detached compressed proof data is separately capped at 128 MiB and does not enlarge the Git
submission archive. It is fetched into private temporary storage, never into the frozen bundle.
Code lengths must be multiples of four. Expanded proof data is capped at 4 GiB; process-tree
memory and overall runtime limits still apply to parsing and checking it. The outer benchmark
limit is 37 MiB. External Yukon
compressed-upload limits still apply; increasing the repository limit does not change those.
Yukon's current separate archive limit is 25 MiB compressed.

## Local reuse and reverification

```sh
python3 scripts/run.py                     # exact host-owned result reuse allowed
python3 scripts/run.py --reverify          # check again; optional checked base allowed
python3 scripts/run.py --fresh-kernel      # check again from an empty kernel environment
python3 scripts/run.py --no-cache          # neither read nor publish acceptance records
```

"Previously accepted" means **this identical validated request**, or **unchanged logical
dependencies**. It does not mean a similar scheme, the same score, a theorem with the same name,
or a solver's claim that somebody already proved it. It does not grant a new leaderboard result.

Exact-result reuse applies only to declarative certificate mode. Source-only submissions always
rebuild/export: arbitrary elaborator IO can observe time, process state, or other inputs that a
source-file hash cannot bind. Their optional worker still checks the current exported proof.

The private acceptance store defaults to `~/.cache/sig-golf/accepted`. Its key binds actual
contract/template/config/checker source bytes, dependency sources and pins, active executable
contents, complete frozen source, claim, verification mode, and the complete certificate bundle.
Git commit attribution is regenerated for the current request; unchanged bytes can reuse a result
after an unrelated commit. Dirty contract or dependency files invalidate it even under unchanged
HEAD. Corrupt, partial, linked, or incompatible entries miss closed. Only the trusted supervisor
publishes successful results, atomically, after all required checks complete.

The store is host-local, not an upload format or portable attestation. A local acceptance record
does **not** authorize the remote server to skip its checks. Private filesystem permissions do
not isolate arbitrary unsandboxed same-UID code; official candidate execution is denied cache
access and writes. The shared Actions tool/dependency cache is still published only by trusted
default-branch setup, before any candidate runs.

## Checked-base worker

For a long-lived **Linux** development or organizer worker, export a generic organizer base:

```sh
python3 verifier/certificate.py base --trusted . --output .work/base.export
python3 verifier/worker.py identity --trusted . --base .work/base.export
```

Use the returned `context_digest` and the installed checker path to start the service:

```sh
python3 verifier/worker.py serve --trusted /absolute/path/to/repo \
  --checker /absolute/path/to/certificate-check --base /absolute/path/to/base.export \
  --context-digest CONTEXT_DIGEST --socket /private/worker-directory/checker.sock
python3 scripts/run.py --worker /private/worker-directory/checker.sock --reverify
```

The worker kernel-checks its generic base once when its checker process starts on the first
request (and again after recycling). Each request independently performs
complete statement, primitive, axiom, and dependency-closure checks. Reuse requires full
structural equality of **every actual base declaration**, including theorem proof bodies,
definition values, inductive groups, and generated constructors/recursors. Any missing/conflicting
base declaration falls back to an empty-environment check. Missing candidate dependencies reject;
the base cannot repair an incomplete certificate. Only the delta is replayed into the immutable
base when all checks match. Candidate environments are discarded and never become the next base.

The supervisor pins checker and context identities, authenticates same-UID Unix peers, and owns
the frozen inputs. The worker has no GitHub token or acceptance-cache write authority. It enforces
bounded messages, input files, process memory, and per-request deadlines, and kills/reseeds after
resource or protocol failures. `--fresh-kernel` bypasses it. Persistent binary kernel snapshots are
not supported. The current ephemeral Actions runner does not keep this service across submissions;
an organizer-managed persistent deployment is needed for cross-job in-memory amortization.

## Timing and resources

Every official run reports challenge build/export, source build/export when applicable, total
checker time, and the checker's separate parse/compare/axiom/kernel times. It writes
`telemetry-verification.json`, and CI retains bootstrap and resource telemetry. Timed Lake jobs
are elapsed durations, not CPU utilization; do not infer an exact parallel fraction from their sum.

Local defaults stay conservative (2 CPUs, 24 GiB). The workflow opts into balanced (4 CPUs, 40 GiB)
inside a 48 GiB guest on the existing 64 GB host. Large is 8 CPUs/80 GiB and needs a larger guest/host.
Explicit numeric overrides validate available CPUs, cgroup/physical memory, and headroom. Lake
task-pool size and per-compiler `-j` are passed separately; a task-pool setting is not a formal hard
bound on compiler subprocess count. No security setting, no-swap policy, or deadline is removed.

### Measured full workload

[Run 37111733072](https://github.com/Layr-Labs/sig.golf/actions/runs/37111733072) accepted the
unchanged submission at score 49,830,768 using four CPUs and 40 GiB. Verification took 47m40s:
source construction 21m30s, export 27s, parse 13s, comparison/axioms 4s, and kernel replay 24m28s.
The same scheme's earlier run took 71m59s, so this single comparison is approximately 34% faster;
it is not a repeated statistical benchmark or a claim about all submissions.

The exported proof measured 730,997,803 bytes and 110,780,561 gzip bytes (level 9). This cannot fit
Yukon's 25 MiB archive limit. Certificate submission therefore needs detached transport for this
workload. Eliminating construction alone leaves roughly 25 minutes of checking, not the earlier
5-15-minute design target. Materially reducing that floor requires reusable checked candidate
lemmas and cheaper-to-check computational proofs; the generic organizer base alone is insufficient.
Native fixtures establish checker/reuse correctness, not that stronger performance claim.

## Merge policy

This repository keeps Yukon promotions manual. Verification emits commit/source/context/artifact
identities so a promotion gate can bind its decision to the exact checked request. It does not add
an auto-merge bot, change promotion ownership, or accept solver-supplied attestations. A PR, claim,
image, checker, or contract change requires matching fresh identities or reverification.
