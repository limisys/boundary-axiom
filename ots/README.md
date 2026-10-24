# ots/ — OpenTimestamps proofs

The timestamp files have moved next to the bytes they seal, in [`../release/`](../release/):

| Proof | Seals | Bitcoin block |
| --- | --- | --- |
| `release/boundary-axiom-f01cf6f-v1.1.0.tar.gz.ots` | the release package | 972871 (merkle root `96023e29…f94e59d`, 2026-10-24 03:42:03 UTC) |
| `genesis/GENESIS.json.ots` | the genesis digest | 972873 (merkle root `90625906…8e83ec5`, 2026-10-24 04:05:48 UTC) and 972874 (merkle root `f22ea8a5…6e9bb249`, 2026-10-24 04:12:06 UTC) |

Both proofs were upgraded from calendar promises to **complete** Bitcoin block-header attestations on 2026-10-24; the earlier `PendingAttestation` state no longer applies. Nothing needs to be re-submitted or awaited. The genesis proof carries two anchors in different blocks because two independent calendars aggregated it — the earlier block is the conservative lower bound, the later one is redundant rather than conflicting.

Verification:

```bash
ots verify -f release/boundary-axiom-f01cf6f-v1.1.0.tar.gz release/boundary-axiom-f01cf6f-v1.1.0.tar.gz.ots
ots verify -f genesis/GENESIS.json genesis/GENESIS.json.ots
```

`ots verify` needs a Bitcoin block source (local node or `--bitcoin-node`). Without one, `ots info <proof>.ots` prints the attested block height and the merkle root the proof commits to; compare that root against a public explorer to confirm the anchor without a node.

This directory is kept as the entry point so existing links to `ots/` keep resolving. The proof files themselves live in `release/` and `genesis/` so that each `.ots` sits beside its target and `ots verify <target>` works from the working directory.
