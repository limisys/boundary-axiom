# release/ — the anchored package

This directory holds the exact bytes that the genesis record is built on. It exists because the packaged archive could not be re-generated bit-identically from git history, so the archived copy itself is the artifact of record.

| File | Size | SHA-256 |
| --- | --- | --- |
| `boundary-axiom-f01cf6f-v1.1.0.tar.gz` | 1,463,311 B | `60b1dbdeef5364bbeddbcdcd240aa35acbfe4763e8824c530adfae77ccc1b64b` |
| `boundary-axiom-f01cf6f-v1.1.0.tar.gz.sha256` | 103 B | checksum file (`sha256sum -c`) |
| `boundary-axiom-f01cf6f-v1.1.0.tar.gz.ots` | 1,807 B | OpenTimestamps proof, Bitcoin block 972871 |

## Why the bytes are in the repository

`git archive --prefix=boundary-axiom-f01cf6f/ f01cf6f | gzip -n` reproduces the *content* of the tree, but not the file: it yields 1,462,369 B / `026670de081b68d9c129ae37517ae9187da5b4d99846cf32bb6b51ef9f7ced9e`, while the anchored package is 1,463,311 B / `60b1dbde…c1b64b`. The compression settings of the original packaging run were not recorded, so a re-generated archive fails the digest check by construction. Anyone verifying this record must use the copy here.

## Verify

```bash
# package digest
sha256sum -c boundary-axiom-f01cf6f-v1.1.0.tar.gz.sha256

# per-file manifest of the packaged tree (183/183)
tar -xzf boundary-axiom-f01cf6f-v1.1.0.tar.gz
(cd boundary-axiom-f01cf6f && sha256sum -c MANIFEST.public.sha256)

# Bitcoin anchor: block 972871, merkle root
# 96023e29396199d7f998b73198fe082536fa2b29b84bd1f8307762231f94e59d, 2026-10-24 03:42:03 UTC
ots info boundary-axiom-f01cf6f-v1.1.0.tar.gz.ots
```

`ots verify` additionally needs a Bitcoin block source; `ots info` alone already prints the attestation height and the expected merkle root, which can be checked against any public explorer.

The genesis record that binds this package (digest `f6a207eb0eda8fd2c0971f30835afbd5a20436eaf603bb8ad461611d060861ac`) is in [`../genesis/GENESIS.md`](../genesis/GENESIS.md).
