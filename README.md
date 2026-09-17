# Erdős #592 — ordinal Ramsey frontier

Which countable ordinals `β` satisfy

\[
\omega^\beta\rightarrow(\omega^\beta,3)^2?
\]

Equivalently: in every red/blue coloring of pairs from `ω^β`, must there be either a red copy of `ω^β` or a blue triangle?

This repository formalizes the ordinal classification framework and reduces the remaining case using explicit literature hypotheses.

## Lean structure

[`research/Erdos592Frontier.lean`](research/Erdos592Frontier.lean) defines five ordinal classes, proves that they partition the relevant exponents, and places named instances in those classes.

[`research/Erdos592Reduction.lean`](research/Erdos592Reduction.lean) imports the known literature verdicts as explicit hypotheses and reduces the unresolved frontier to the class with three indecomposable summands.

Under those dated literature inputs, the least remaining instance is

\[
\beta=\omega^3.
\]

The package proves the `β=0` Ramsey instance directly; the five external Ramsey verdicts are not reproved in Lean here.

## Files

| File | Role |
|---|---|
| [`Erdos592Frontier.lean`](research/Erdos592Frontier.lean) | Partition of ordinal cases and named instances |
| [`Erdos592Reduction.lean`](research/Erdos592Reduction.lean) | Reduction using explicit literature hypotheses |
| [`Erdos592Audit.lean`](research/Erdos592Audit.lean) | Declaration/dependency audit |
| [`receipts/campaign.json`](research/receipts/campaign.json) | Toolchain and literature snapshot |

## Verification

```sh
python verification/verify_source.py
```

The historical environment is pinned in the campaign receipt: Lean `v4.31.0-rc1`, Mathlib commit `919544d4309104b3f19724b0e6e48c701d27948f`.

The formal framework and reduction are complete at their stated hypotheses; the `β=ω^3` frontier and the full classification remain unresolved in this repository.

Author: Jared Wilder. License: Apache-2.0.
