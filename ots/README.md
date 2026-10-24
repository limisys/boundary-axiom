# OpenTimestamps proofs

Anchored artefacts for this release. Bitcoin attestation upgrades within a few hours;
run `ots upgrade <file>.ots` to fold in the completed attestation.

| file | sha256 |
| --- | --- |
| `boundary-axiom-f01cf6f-v1.1.0.tar.gz` | `60b1dbdeef5364bbeddbcdcd240aa35acbfe4763e8824c530adfae77ccc1b64b` |

Verify:

```
sha256sum -c boundary-axiom-f01cf6f-v1.1.0.tar.gz.sha256
ots verify boundary-axiom-f01cf6f-v1.1.0.tar.gz.ots
```

The snapshot itself is reproduced by `git archive --prefix=boundary-axiom-f01cf6f/ f01cf6f`.
