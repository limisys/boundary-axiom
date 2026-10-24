# Genesis record — v1.1.0

This directory fixes the complete published package of **The Mind Has a Boundary** at a single digest and anchors that digest in time. It is the reference point for any later claim about priority or authorship of this corpus.

## Genesis digest

| Field | Value |
| --- | --- |
| Package | `boundary-axiom-f01cf6f-v1.1.0.tar.gz` (1,463,311 B) |
| Package SHA-256 | `60b1dbdeef5364bbeddbcdcd240aa35acbfe4763e8824c530adfae77ccc1b64b` |
| Commit | `f01cf6f7dffd65b0d835e0139912d66dc734c4d7` (tag `v1.1.0`) |
| Files in package | 184 |
| Tree Merkle root | `161e48a62252b59247abae510c65771f9c63ca43956804f70fd98ad3ee39eaba` |
| Per-file manifest (frozen, packaged tree) | `MANIFEST.public.sha256`, 183 entries, SHA-256 `1fb0301132e66edfd20d0286691db0f78d2a83e9029ee5fd35cf77fdb45fa59c` |
| **Genesis digest (this record)** | **`f6a207eb0eda8fd2c0971f30835afbd5a20436eaf603bb8ad461611d060861ac`** |

The genesis digest is the SHA-256 of `GENESIS.json`, which binds the rows above into one file.

## Where the anchored bytes live

The released bytes are in the repository, not only in a build directory:

| File | Note |
| --- | --- |
| `release/boundary-axiom-f01cf6f-v1.1.0.tar.gz` | the anchored package, 1,463,311 B, SHA-256 `60b1dbde…c1b64b` |
| `release/boundary-axiom-f01cf6f-v1.1.0.tar.gz.sha256` | checksum file for the above |
| `release/boundary-axiom-f01cf6f-v1.1.0.tar.gz.ots` | OpenTimestamps proof, upgraded to a complete Bitcoin attestation |

**Bit-identical reproduction from git is not possible.** `git archive --prefix=boundary-axiom-f01cf6f/ f01cf6f | gzip -n` produces 1,462,369 B with SHA-256 `026670de081b68d9c129ae37517ae9187da5b4d99846cf32bb6b51ef9f7ced9e`, which is **not** the anchored 1,463,311 B / `60b1dbde…`. The compression settings of the original packaging run are not recorded, so a re-generated archive will not match. Verify the released copy; do not re-generate and compare.

## Timestamps — both anchors complete

| Anchor | Evidence | Time | Status |
| --- | --- | --- | --- |
| RFC 3161 TSA (freetsa.org) | `GENESIS.json.tsr` (request: `.tsq`) | **2026-10-24 03:48:36 GMT**, serial `0x0965B6C4` | Granted, signature verified against `tsa-cacert.pem` |
| OpenTimestamps (Bitcoin) — genesis record, anchor 1 | `GENESIS.json.ots` | **Bitcoin block 972873**, merkle root `90625906d9233b07692b176a16b5d11b1009eac87b2978f793dba69be8e83ec5`, block time 2026-10-24 04:05:48 UTC | **Complete** (`BitcoinBlockHeaderAttestation(972873)`) |
| OpenTimestamps (Bitcoin) — genesis record, anchor 2 | `GENESIS.json.ots` | **Bitcoin block 972874**, merkle root `f22ea8a5f3bf05d2d8a064c1d5e33f38523361910c97dcf3695a2b0e6e9bb249`, block time 2026-10-24 04:12:06 UTC | **Complete** (`BitcoinBlockHeaderAttestation(972874)`) |
| OpenTimestamps (Bitcoin) — package | `release/boundary-axiom-f01cf6f-v1.1.0.tar.gz.ots` | **Bitcoin block 972871**, merkle root `96023e29396199d7f998b73198fe082536fa2b29b84bd1f8307762231f94e59d`, block time 2026-10-24 03:42:03 UTC | **Complete** (`BitcoinBlockHeaderAttestation(972871)`) |

All three Bitcoin merkle roots were independently re-read from a public block explorer. The genesis record carries two anchors in different blocks because two independent calendars aggregated it; the earlier block (972873) is the more conservative lower bound, and the later one (972874) is redundant rather than conflicting. The block times frame the packaging run (03:42:03 UTC) and the genesis record (03:48:06 UTC create / 03:48:36 UTC TSA / 04:05:48 and 04:12:06 UTC anchors).

## Two manifests, two scopes

| Manifest | Entries | Covers | Use it from |
| --- | --- | --- | --- |
| `MANIFEST.public.sha256` | 183 | the packaged tree at `f01cf6f`, **frozen**; SHA-256 `1fb0301132e66edfd20d0286691db0f78d2a83e9029ee5fd35cf77fdb45fa59c` (the value bound in `GENESIS.json`) | inside the extracted package directory only |
| `MANIFEST.attestation.sha256` | 195 | the current `main` worktree, including `genesis/`, `ots/`, `release/` and page-metadata updates | repository root |

Why they are separate: commits after `f01cf6f` (i) added attestation files, and (ii) updated page metadata in `site/evidence.html`. Folding those into `MANIFEST.public.sha256` would change its SHA-256 away from the value anchored in `GENESIS.json`, breaking the self-consistency of the record — which is exactly what happened between `f01cf6f` and `f89313e`. The packaged manifest is therefore restored verbatim to its `f01cf6f` bytes, and every later file is registered in the attestation manifest instead.

Consequence to be explicit about: `sha256sum -c MANIFEST.public.sha256` run at the repository root will report `site/evidence.html` as FAILED, because the repository copy of that page has since been updated. It passes 183/183 inside the extracted package. Use the attestation manifest for the repository tree.

## Verify

```bash
# 1. the anchored bytes
sha256sum -c release/boundary-axiom-f01cf6f-v1.1.0.tar.gz.sha256

# 2. the packaged tree — must run inside the extracted directory
tar -xzf release/boundary-axiom-f01cf6f-v1.1.0.tar.gz
(cd boundary-axiom-f01cf6f && sha256sum -c MANIFEST.public.sha256)   # 183/183 OK

# 3. the current repository tree
sha256sum -c MANIFEST.attestation.sha256

# 4. genesis digest and RFC 3161 token
sha256sum -c genesis/GENESIS.sha256
openssl ts -verify -data genesis/GENESIS.json -in genesis/GENESIS.json.tsr -CAfile genesis/tsa-cacert.pem

# 5. both Bitcoin anchors (complete; -f points at the anchored bytes)
ots verify -f release/boundary-axiom-f01cf6f-v1.1.0.tar.gz release/boundary-axiom-f01cf6f-v1.1.0.tar.gz.ots
ots verify -f genesis/GENESIS.json genesis/GENESIS.json.ots
```

`ots verify` needs a Bitcoin source for the block header. Without a local node, `ots info <proof>.ots` already shows the attestation and the expected merkle root, which can be compared against any public explorer.

## Scope note

Commits after `f01cf6f` add attestation files (`genesis/`, `ots/`, `release/`), register them in `MANIFEST.attestation.sha256`, and update page metadata in `site/`. None of them alter the anchored bytes or the packaged tree: the package SHA-256 and the tree Merkle root always refer to `f01cf6f`, and `MANIFEST.public.sha256` is kept byte-identical to its packaged version.
