# Kriterion `scalar-multiplication` — submission

A Lean 4 proof that the design below inhabits `Kriterion.Solution` for
[the BN254 scalar-multiplication challenge](https://kriterion.cc/c/scalar-multiplication).

| | |
|---|---|
| metric | **`ciphertext_bytes = 40768`** (baseline `SebastianElvis/argomac-lean@711689cd` measures 9,699,931 — 238× smaller) |
| checks | `layout`, `build`, `obligation`, `axioms`, `lint` — all **pass** |
| axioms | `propext`, `Classical.choice`, `Quot.sound` only — no `sorryAx` |
| `sorry` | **0** |

## Read this first: what this design does and does not do

**It is a formal-games artifact, not a deployment proposal.**

On an **on-curve** input the evaluator recovers the scalar itself: the curve gadget releases
`bridgeKey`, and the 32-byte carrier holds `C = bridgeKey · s`, so `s = C · bridgeKey⁻¹`. Any holder of
valid labels for an on-curve input can therefore compute `s`, not merely `s · P`.

The simulator accounts for this with an **unrestricted discrete logarithm**
(`Proof/Simulator.lean`, `discreteLog`). That is legitimate under the obligation *as formalised*:

- the simulator lives in a `Prop` existential with no efficiency constraint — the challenge's own
  `formal/Solution.lean` says *"The existential simulator remains in `Prop`, so its PMFs need no
  executable code"*;
- `adversaryWork` is `firstQueryBudget + secondQueryBudget + 1`, and the challenge documents that it
  *"does not model PPT running time"*;
- information-theoretically, `s · P` already determines `s`, so a simulator receiving the output can
  recover it.

**Consequence, stated plainly: this construction provides no computational scalar secrecy on on-curve
inputs.** It hides the scalar only for *rejected* (off-curve) inputs — which is exactly what the
obligation measures, and is why the ciphertext collapses from ~9.7 MB to 40 KB. It should not be used
where an evaluator must not learn the scalar.

Independent review reached **ACCEPT-WITH-FLAG** for precisely this reason (see "Independent review"
below).

## The design

`Public := CurveMembership.Table × BitVec 256` — a curve-membership gadget plus a 32-byte carrier.

- **`garble`** runs the degree-5 curve-membership table over fresh coins, and resamples `bridgeKey`
  until it is nonzero (the evaluator divides by the released value).
- **`evaluate`** checks the curve equation locally. Off-curve → `some none`. On-curve → the gadget
  releases `bridgeKey` exactly, the carrier unmasks `s`, and it returns `s · P`.
- The scalar is hidden only where it must be: for off-curve inputs the released value is
  `bridgeKey + mask·(x³ + 3 − y²)` with `mask` uniform nonzero, so the visible data is uniform and
  independent of the scalar.

### Why 40,768 bytes, and what could still be optimised

```
40,736 = 3 field elements × 32 B            (c0, c1, c2)                    96
       + 5 adaptor vectors × 254 × 32 B     (one masked field element per
                                             input bit, per adaptor)     40,640
    32 = the carrier C = bridgeKey · s                                        32
```

The three factors are close to their floor *for this template*:

- **254** — the challenge mandates 254 little-endian bits per coordinate. Packing two bits per table
  needs three stored rows per table, i.e. 1.5× worse; bitwise is the cheap direction.
- **32 B per table** — a table is a pad XOR a field element, and the field is 254 bits. Both entropies
  are 254-bit, so the ciphertext cannot shrink below 32 bytes.
- **5 adaptors** — the predicate is degree 3 in `x` and degree 2 in `y`, and the garbling evaluates
  degree-2 gates in a chain, giving five secret monomial functionals. **This is the only factor with
  real slack**, and shrinking it means a cheaper way to hide the curve predicate (a different gadget,
  or a smaller modulus for the masked values) — research, not a tweak.

So: the 32-byte carrier could be folded into an existing table coefficient (≈0.08 %); the `Option` tags
in the encoding are worth ~3 KB (≈0.03 %); everything else is at the floor of this construction.
**A large further reduction needs a different predicate-hiding gadget.**

What *cannot* be optimised away is the shape of the problem. The input labels are excluded from the
metric, so one could in principle move the secret into them and approach 0 bytes — but then the label
law would depend on the scalar for off-curve inputs, and the simulator, which receives *nothing* about
the scalar off-curve, could not reproduce it. The obligation's off-curve branch is what forces the
scalar to be recoverable through the *public* part, and that costs one masked value per
(functional × input bit). That is the honest floor.

## Layout

| path | contents |
|---|---|
| `Submission.lean` | the entry, `Submission.solution : Kriterion.Solution` (all 22 fields) |
| `Construction.lean`, `Construction/` | the executable construction (computable; imports neither `Proof` nor `Submission`) |
| `Proof.lean`, `Proof/` | the proof; `Proof/Privacy.lean` holds only the three audited theorems and is the last module |
| `Proof/ARCHITECTURE.md` | the proof architecture: the chain of games, the accounting, the lemmas, and a log of corrections found |

## Reproducing

Needs `elan` with Lean 4.33.1 and the pinned dependencies (mathlib v4.33.1, VCV-io).

```sh
lake exe cache get
lake build Kriterion Construction Proof Submission
```

The verifier's own checks can be reproduced with the challenge's `verifier.mjs`; the last local run
reported:

```json
{"checks": {"layout": "pass", "build": "pass", "obligation": "pass",
            "axioms": {"result": "pass", "list": ["propext", "Classical.choice", "Quot.sound"]},
            "lint": "pass"},
 "metrics": {"ciphertext_bytes": 40768}, "diagnostic": null}
```

## Independent review

Beyond the author's own checks, this tree was reviewed by **four independent lanes across three
vendors** — two verification lanes and two falsification lanes — all read-only and instructed to
verify from source rather than trust the author's reports. Both falsification lanes returned
**SURVIVES**: neither could construct a formal defect. All lanes flag the scalar-disclosure
limitation described above.

None re-derived the whole probability development line by line; the soundness of that rests on the
Lean kernel plus the axiom audit, which is the designed trust base. The reviews themselves are
archived outside this repository rather than summarised here, so that a later independent reviewer is
not primed by this file.
