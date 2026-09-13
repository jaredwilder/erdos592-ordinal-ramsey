# Erdős #592: the ordinal Ramsey frontier

Which countable ordinals `beta` satisfy
`omega^beta -> (omega^beta,3)^2`? In a red/blue edge coloring, this asks for
either a red clique of the specified order type or a blue triangle.

This repository gives Jared Wilder's ordinal framework, conditional
reductions and Lean audit a focused home.

## Start here

| File | Purpose |
|---|---|
| [Frontier](research/Erdos592Frontier.lean) | Defines the partition relation and five ordinal classes; proves the classes form a partition and places named instances |
| [Reduction](research/Erdos592Reduction.lean) | Reduces the remaining question using explicit literature hypotheses |
| [Audit](research/Erdos592Audit.lean) | Declaration dependency checks |
| [Campaign receipt](research/receipts/campaign.json) | Exact scope, literature attributions, environment and open obligations |
| [Build and axiom logs](research/receipts/) | Historical verification evidence and dated problem snapshot |

## Formal scope

The Lean framework proves the ordinal partition and supporting facts,
including the `beta=0` Ramsey instance. It does **not** prove the five
literature verdicts about the Ramsey relation. Those enter the reduction as
explicit assumptions or documentation.

Under the dated literature record, the class with three indecomposable
summands is the remaining frontier; `beta=omega^3` is its least instance.
The package does not solve that instance or the full classification.
The campaign records an audit of 28 declarations with the listed standard
axioms. No fresh Lean compilation was run during this promotion.

## Reproduce and trace

```sh
python verification/verify_source.py
```

The source-byte check is independent of Lean compilation. The original
environment is pinned in [campaign.json](research/receipts/campaign.json):
Lean `leanprover/lean4:v4.31.0-rc1`, Mathlib commit
`919544d4309104b3f19724b0e6e48c701d27948f`.
Compile Frontier, then Reduction, then Audit with the resulting module
directory on `LEAN_PATH` inside that Mathlib environment.

All eight research files are exact copies from the
[campaign archive](https://github.com/jaredwilder/erdos-campaign-archive/tree/main/campaigns/erdos592-close-2026-09-05).
[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) pins the source commit, paths,
Git blobs, byte counts and SHA-256 hashes. This is the preferred problem-level
entry; dated literature snapshots and original archive links remain provenance.

Author: Jared Wilder. Source campaign: 2026-09-05. Focused release: 2026-09-13.
License: Apache-2.0, inherited from the public source.
