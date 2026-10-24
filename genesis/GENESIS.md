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
| Per-file manifest | `MANIFEST.public.sha256`, 183 entries, SHA-256 `1fb0301132e66edfd20d0286691db0f78d2a83e9029ee5fd35cf77fdb45fa59c` |
| **Genesis digest (this record)** | **`f6a207eb0eda8fd2c0971f30835afbd5a20436eaf603bb8ad461611d060861ac`** |

The genesis digest is the SHA-256 of `GENESIS.json`, which binds the rows above into one file.

## Timestamps

| Anchor | Evidence | Time | Status |
| --- | --- | --- | --- |
| RFC 3161 TSA (freetsa.org) | `GENESIS.json.tsr` (request: `.tsq`) | **2026-10-24 03:48:36 GMT**, serial `0x0965B6C4` | Granted, signature verified against `tsa-cacert.pem` |
| OpenTimestamps (Bitcoin) | `GENESIS.json.ots` | — | PendingAttestation; run `ots upgrade` after confirmation |

The TSA time is attested at issuance. The Bitcoin anchor becomes independently verifiable once the containing block is confirmed.

## Verify

```bash
sha256sum GENESIS.json                     # f6a207eb...0861ac
sha256sum -c GENESIS.sha256
ots verify GENESIS.json.ots                # Bitcoin attestation (after upgrade)
openssl ts -reply -in GENESIS.json.tsr -text | head -20
openssl ts -verify -data GENESIS.json -in GENESIS.json.tsr -CAfile tsa-cacert.pem

# package level
sha256sum boundary-axiom-f01cf6f-v1.1.0.tar.gz
tar -xzf boundary-axiom-f01cf6f-v1.1.0.tar.gz
cd boundary-axiom-f01cf6f && sha256sum -c MANIFEST.public.sha256
```

## Scope note

Later commits on `main` only add attestation files (`ots/`, `genesis/`) and edit page metadata (`site/evidence.html`). None of them alter the tree that produced the digests above; the package SHA-256 and Merkle root always refer to `f01cf6f`.
