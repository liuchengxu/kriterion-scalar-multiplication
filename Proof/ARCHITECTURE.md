# Proof architecture for `hybridGame_close_to_idealGame`

Status of the tree: every obligation is proved except the single `sorry` at
`Proof/Privacy.lean`, theorem `hybridGame_close_to_idealGame` (statement must stay
byte-identical). This document is the plan for closing it, the pieces that are already
machine-checked, and the constant it produces. The next slice must inherit it rather than
re-derive it.

Slice 3d closed P5 (the deferral, `Proof/Deferred.lean`), P9a (`R(b)` as a `PMF Bool`,
`Proof/ReferenceGame.lean`) and the generic and stage-1 halves of P3 (`Proof/Hidden.lean`), and
corrected the accounting of §4 (crude `K ≤ 10`, see below). The deferral was the only place the
architecture could have been unformalizable; it is a plain `ENNReal.tsum_comm` argument.

Slice 3e closed the per-coordinate half of P6 (`Proof/Distance.lean`: the total-difference tools,
the mask law and the hash fiber law) and the structural core of P7
(`Proof/DeferredSteering.lean`: the programmed reference view releases every selected output, the
steering is the shift at `(x7, 0)`, and the double programming is the reference programming on a
reparametrised permutation). Nothing in step 7 contradicted the chain.

Slice 3f closed **all of P6** (`Proof/Product.lean` + `Proof/GateProduct.lean`: the tensorisation),
**all of P7** (`Proof/GateProduct.lean`: the fiber marginal; `Proof/FreshBridge.lean`: the
`programAll` → `programIndices` bridge) and **all of P3** (`Proof/SecondStage.lean`: the stage-2
bound). **Every machinery item of the chain is now machine-checked; only the assembly (P9b + P10)
is open.** Nothing in the tensorisation, the bridge or the stage-2 bound contradicted the chain,
and no constant moved.

Slice 3g closed **all of P9b** (`Proof/GameShape.lean`) and started P10. Both ideal games are now
unfolded into the two-stage shape of §4 (`simulatedGame_eq`, `hybridGame_eq`), the tape's unused
curve coordinates and its fixed-key oracle can be marginalised (`uniform_bind_setCurve`,
`uniform_bind_setOracle`), and the `unread` hypothesis of `secondStage_hidden_le` is discharged for
all three second stages (`hybridStageTwo_unread`, `referenceStageTwo_unread`,
`simulatedStageTwo_unread`). The assembly layer of P10 exists (`Proof/Chain.lean`: the three kinds
of hop and the accounting, machine-checked at `K = 10` and `ε₀ < 2^-119`), and the first hop's
algebra is proved (`Proof/Reparametrise.lean`). **P10 itself is still open: the eight steps of §4
are not yet chained, so `hybridGame_close_to_idealGame` still carries the single `sorry`.**

Slice 3h did **steps 1 and 3 of §4 on the `H` side** (`Proof/HybridChain.lean`): the hybrid game
is reparametrised exactly into the reference table of fresh per-gate digests and pads (step 1),
and the two oracle hops of step 3 are charged, giving the machine-checked

```lean
theorem advantage_hybridGame_digestedReference_le :
    advantage (idealGame … (hybridSimulator scalar) …) (digestedReference scalar …)
      ≤ 4 * (q₁ + q₂) / 2 ^ 128
```

where `digestedReference` is `R(c/s)` **except** that its mask is still the tape's nonzero
`curveMask` and its fiber sample is still the fresh 384-bit digest family.

Slice 3i closed **step 2 of the `H` side and the identification with `R(c/s)`**
(`Proof/HybridReference.lean`), so the whole hybrid side of the chain is now machine-checked:

```lean
theorem advantage_hybridGame_referenceGame_le :
    advantage (idealGame … (hybridSimulator scalar) …)
        (referenceGame (fun carrier => ((mulScalar scalar).symm carrier).value) …)
      ≤ 4 * (q₁ + q₂) / 2 ^ 128 + sideOneTime
```

The missing tool of step 2 — a **marginal lemma for a product law** — was built first
(`productPMF_bind_congr` in `Proof/Product.lean`, `uniformHashFibers_bind_congr` in
`Proof/GateProduct.lean`). **The whole `S` side (steps 4–7) and the final assembly are still
open**, so `hybridGame_close_to_idealGame` still carries the single `sorry`. See "What P10
still has to do" and the constant assignment below.

## 1. The correction that drives the architecture

The slice-3b analysis of the three cases (A off-curve, B on-curve/bit false, C on-curve/bit
true) is correct as pen-and-paper coupling reasoning, but it **cannot be built as a bijection
on the pre-sampled `(tape, carrier)` space**:

* the case split (`decodePoint input`), the set of hidden ("unselected-label") points, the
  steering bit, and the case-A shift `δ = (c/s − u) / Δ(input)` all depend on the input;
* the adversary chooses that input **adaptively at the end of stage 1**, after it has already
  queried the stage-1 oracle, which in the hybrid game is the very tape the coupling would
  have to rewrite.

Any correct formal proof must first **defer the hidden randomness past stage 1**: sample only
what stage 1 can see, run stage 1, and only then sample (or transform) the rest, per input.
In a fully pre-sampled model that deferral is a change of coordinates on the sample space
(`P4` below) plus a bind-swap (`P5`). Both games get the same treatment, and the comparison
happens in the deferred form. Do not attempt a direct `H ↔ S` sample-space coupling.

`P5` is proved in the **transfer form** (`twoStageGame_congr`): a two-stage game
`twoStageGame law view rest stage1 stage2 = law >>= ω ↦ stage1 (view ω) >>= r ↦ stage2 (view ω)
(rest r ω) r` depends on `law` only through the joint laws `map (ω ↦ (view ω, rest r ω)) law`, one
per first-stage result `r`. So step 7 needs no explicit conditional law: it is
`twoStageGame_congr` with `view = (tape, c, table)`, `rest r = selected outputs of r.inp`, and the
per-input joint-law equality supplied by `P4`. The factored form of the doc
(`twoStageGame_eq_deferredGame`, hidden law `ν r v`) is also proved but is not needed.

## 2. The reference game `R(b)`

Fix a bridge key `b : BaseField`. The reference sample is

* `tape : Garbling.Randomness` — used only for `fixedKeyOracle π`, `inputMacKey K`, `encOracle`,
  `hashOracle` (its `bridgeKey`, `curveMask`, `curveR1`, `curveR2` are ignored);
* `raw : Coordinates` = `(mask, r1, r2, hash : GateValues F, pad : GateValues (BitVec 256))`,
  uniform on all of `Coordinates` (`mask` ranges over all of `F`, not `F*`);
* `carrier c : NonZeroBase`.

The public value is `(raw.table b K, carrierBits c)` where `Coordinates.table` is
`CurveMembership.garble b mask r1 r2 (secretOracles hash pad) K`: each gate's oracle returns the
fixed field element `hash a i` as the "hash" and `pad a i ^^^ fieldBytes m` as the "encryption",
**ignoring the label**. So the table does not depend on `K`, and the honest labels are never
needed to garble.

* Stage 1 runs the adversary with `idealOracle` (logging) on the **unprogrammed** view
  `(π, enc, hashOracle)`.
* After the input `inp` is chosen, `R(b)` programs `π` **only at the selected labels**: for gate
  `(a, i)` with selected bit `β`:
  * `β = false` (selected `F_i`): the three hash slots at `F_i` are programmed to a
    `uniformHashFiber (o a i)` sample, where `o a i` is the selected output (`= hash a i`);
  * `β = true` (selected `T_i`): the two pad slots at `T_i` are programmed to
    `rows a i ^^^ fieldBytes (o a i)` (`= pad a i`, since `o a i = slope a + hash a i`).
  Unselected labels are never programmed and never used.
* Stage 2 runs on the programmed view with the honest labels
  `Lamport.selectedLabels (K.encodeAffine inp)`.

`R(b)` is `referenceGame bridge adversary parameter auxiliary` in `Proof/ReferenceGame.lean`,
with `bridge : NonZeroBase → BaseField` the bridge key as a function of the carrier (`R(c/s)` is
`bridge := fun c => c / s`). Stage 2 is `referenceStage2`: it samples `uniformHashFibers o` (one
384-bit fiber sample per gate, `HashFibers`), builds `selectedPrograms K inp o rows fibers :
Programs` (`FixedKeyIndex → Option (Block × Block)`: hash slots of `false` gates at the selected
label to the fiber chunks, pad slots of `true` gates to `rows ⊕ fieldBytes o`; everything else
`none`), and runs `decide` on `programSelected`, i.e. the stage-1 state with `programIndices`
applied to its fixed-key oracle. Programming is **unconditional** (`programmed π ℓ r = π.trans
(swap (π ℓ) r)`, the same shape as `programAt` and `programPermutation`); the simulator's
`programIfFresh` agrees with it on every good log, which is the only place the two are compared.

## 3. Why `R(b)` and the visible laws (`P4`, proved)

For a fixed input the raw coordinates are in bijection with the **middle coordinates**
`(mask, c1, c2, o, rows)` (`middleEquiv input`), where `o a i` is the selected output of gate
`(a, i)` (`selectOutput`), `c1 = mask + r1`, `c2 = −mask + r2`, and `rows` are the table rows.
The released row is (`Coordinates.table_c0_eq`, derived from `evaluateEncoded`)

```
c0 = b + mask · curveGap(inp) − offsetTerm(inp, middle),
curveGap(inp) = x³ + 3 − y²,
offsetTerm    = c1·x³ + c2·y² + O₃·x² + O₄·y + O₅·x + O₆ + O₇,   O_a = fromBits (o a).
```

Everything the adversary can ever see in `R(b)` is a function of
`visibleCoordinates b K inp raw = (c0, c1, c2, o, rows)` (plus `π`, `K`-selected labels, `c`,
which are independent of `raw`). Hence:

* **Off the curve** (`curveGap ≠ 0`): `mask ↦ c0` is a bijection, so
  `map (visibleCoordinates b K inp) uniform = uniform` — **independent of `b`**
  (`visibleCoordinates_offCurve`). This is the whole content of "case A": no shift of
  `(mask, r1, r2)` and no per-gate hidden-value shift is needed once the hidden randomness is
  deferred; the 1270-gate coupling of the slice-3b report collapses to this one line.
* **On the curve** (`curveGap = 0`): `c0 = b − offsetTerm`, `mask` is free, and shifting the
  selected output of adaptor `x7`, position `0` by `δ` (`shiftMiddle δ`) changes `offsetTerm`
  by `+δ` (`offsetTerm_shiftMiddle`, coefficient exactly one), so
  `map (shiftMiddle δ) (map (visible b) uniform) = map (visible (b + δ)) uniform`
  (`visibleCoordinates_onCurve`). This is "case B/C": steering is exactly the shift
  `δ = c/s − u`, and it acts on the visible law, not on the tape.

Both theorems are unconditional on the input except for the curve test; they need no
hypothesis outside the design (`[FieldCertificate]` for division off the curve only).

## 4. The chain of games

Write `H` for the hybrid game (table for `c/s`, honest oracle throughout), `S` for the simulated
game (table for `u = tape.bridgeKey`, steering at `(x7, 0)`), `q₁, q₂` for the two budgets,
`q = q₁ + q₂`, `p = baseFieldModulus`.

**H side.**
1. `H ≅ H'`: reparametrize `π` by `programFamily` (`P1`, exact): `π_H = π°` programmed at
   every *used* label (`F_i` at hash slots, `T_i` at pad slots) to fresh uniform values `ρ`;
   the table is then `T̃(c/s, mask, r1, r2, red ρ_hash, ρ_pad)`.
2. `H' ≈ H''`: `mask ∈ F*` → `mask ∈ F` (TV `1/p`), and 384-bit `ρ_hash` → (`hash ∈ F`, then a
   fiber sample) (TV ≤ `p/2^384 ≈ 2^-131` per gate, 1270 gates) — `P6`, data processing.
3. `H'' ≈ R(c/s)`: the two games differ only in the oracles: stage 1 (`π_H` vs `π°`) at the
   programming points of every used label, stage 2 (`π_H` vs `π°` programmed at selected labels
   only) at the programming points of the *unselected* labels. Per log entry at most **2**
   points per direction (`{ℓ, π°⁻¹(ρ ⊕ ℓ)}` forward, `{ρ ⊕ ℓ, π°(ℓ)}` inverse). Bounded on the
   `R` side, where the labels are independent of the stage-1 view and the unselected labels are
   independent of the stage-2 view: `≤ 2q/2^128` (`P2` + `P3`).

**S side.**
4. `S ≅ S'`: same reparametrization (`P1`).
5. `S' ≈ S⁺`: replace the stage-1 oracle by the unprogrammed `π°`: `≤ 2q₁/2^128` (`P2` + `P3`).
6. `S⁺ ≈ S⁺⁺`: replace the stage-2 honest programming at the *unselected* labels by nothing:
   `≤ 2q₂/2^128`. (`steer` reads only selected-label slots, so it is unaffected.)
7. `S⁺⁺` in deferred form (`P4` + `P5`) is `R(u)` plus steering. Off the curve
   `visible(u) = visible(c/s)` in law (`visibleCoordinates_offCurve`). On the curve, `steer`
   is exactly `shiftMiddle (c/s − u)` on the visible data (`P7`: `wanted = position + target −
   current`, `position = o x7 0`, `current = u` by `evaluateEncodedOnCurve`), so
   `visibleCoordinates_onCurve` gives `visible(c/s)`; the fiber sample of `S` is the fiber sample
   of `R`, and the double programming at `(x7,0)` (honest, then steered) is the single
   programming of `R` after the reparametrization `π° ↦ swap(r₁, r₂) ∘ π°` (2 more hidden
   points per direction at those five indices, stage 1 only) — `P7`.
8. Triangle inequality (`advantageTriangle`, `event_difference_le`) and `P8`.

**Accounting (corrected in slice 3d).** Each identical-until-bad hop is one application of
`bind_identical_until_bad` + `run_idealOracle_agree`, whose `good` condition ranges over the
**whole final log**: a stage-2 re-query of a stage-1 entry that hit a hidden point would be
answered differently by the two views, so the stage-1 entries must also be charged against the
stage-2 hidden set. Hence every hop costs `2·q/2^128` with `q = q₁ + q₂`, not `2·q₂`. The hops:
step 3 as two hops via the mixed game (stage 1 on `π°`, stage 2 on `π_H`): `2q + 2q`; step 5:
`2q`; step 6: `2q`; step 7's `swap(r₁, r₂)` reparametrization of `π°` at the five `(x7,0,·)`
indices: `2q` (it is *not* inside step 5's count: merging it into step 5 gives 3 points per
direction at those indices, `K = 3` for that hop, which is no better). Crude total
`advantage ≤ 10q/2^128 + ε₀`, i.e. **K ≤ 10** (`K = 4` was an undercount), with
`ε₀ ≤ 2·1270·2^-131 + 3/p < 2^-119`. `workPerAdvantage_of_le` (proved) closes the obligation
from `K ≤ 2^28` and `ε₀ ≤ 2^-101`; the margin to the wall is `2^24`.

The stage-1 half of each bad bound is `firstStage_hidden_le` (`Proof/Hidden.lean`): for any game
that samples the label key up front and whose first stage runs on data independent of the key,
the mass of "some stage-1 entry `e` has `keyLabel K (which e) ∈ hidden(data, e)`" is at most
`k·q₁/2^128` when every `hidden` set has at most `k` points. The hidden sets of one programmed
permutation are `forwardHidden`/`inverseHidden` (`k = 2`, `hiddenLabels_card`), and
`publicAnswer_programIndices_single` is the matching "views agree off the hidden set" fact for
`run_idealOracle_agree`. The stage-2 half (the unselected label of the entry's gate, which the
stage-2 run does not read) needs the per-index involution `setKeyLabel` at that one label
instead of the whole key; `uniform_bind_setKeyLabel` / `uniform_keyLabel_mem` are in place.

**Corrections from slice 3e.**

* The reparametrisation of step 7 touches only the steering-gate slots that the reference game
  actually programs: the **three** hash slots when the steering bit is `false`, the **two** pad
  slots when it is `true` — never five at once (`steerPrograms`, `programIndices_steerPrograms`).
  The hidden set of the swap is still 2 points per direction (`{π°⁻¹(r), π°⁻¹(s)}` forward,
  `{r, s}` inverse), so `K ≤ 10` is unchanged.
* `programIndices_steerPrograms` needs `π° ℓ ≠ r` and `π° ℓ ≠ s` at those slots (otherwise the
  transposition of the honest programming is the identity and the two programmings do not
  compose). This is a **one-time** event, not a per-query one: `r` and `s` are fresh uniform
  chunks, so its mass is at most `6/2^128 < 2^-125`. Add it to `ε₀`, which stays below `2^-119`.
* `bind_apply_sub_le` bounds an outcome probability by the **total difference** (twice the total
  variation), so the one-time terms of §4 are charged at `2/p` for the mask and `2 p/2^384` per
  gate. Both are already inside the `ε₀ ≤ 2^-101` the arithmetic tail needs.
* The 384-bit-vs-field replacement is a replacement of a **product** of 1270 independent
  coordinates, so it needs a tensorisation step that the per-coordinate fact does not supply.
  The recipe: `HashFibers o ≃ Π gates, HashFiber (o gate)` (`Equiv.subtypePiEquivPi`), so both
  laws are products of one coordinate law; define the interpolating laws by
  `PMF.ofFintype (fun values => ∏ gate, lawOf gate (values gate))` (sum-to-one by
  `Finset.prod_univ_sum` and `Fintype.piFinset_univ`), and swap one coordinate at a time by
  `Finset` induction, each step costing `hashFiber_total_difference` by the same product-sum
  exchange.

**Corrections from slice 3f.**

* The tensorisation recipe above is exactly what was built, on the index type
  `Gate = CurveAdaptor × Fin coordinateBitCount` (`card_gate : Fintype.card Gate = 1270`) with
  `gateCurry : (Gate → Value) ≃ GateValues Value` carrying it to the nested function type.
  The one-coordinate swap needed no explicit interpolating family beyond
  `Function.update`: `totalDifference_productPMF_update` is an **equality** computation (split off
  the coordinate, sum the rest to one), and the `Finset` induction over the mixture
  `if index ∈ chosen then first index else second index` is the only interpolation.
* The step-2 charge is now a single machine-checked constant:
  `hashFibers_total_difference ≤ 1270 · p / 2^384`, i.e. `< 1270 · 2^-130 < 2^-119`, which is the
  `2 · 1270 · 2^-131` of §4 written without the factor-of-two bookkeeping. `ε₀ < 2^-119` and
  `K ≤ 10` are unchanged.
* The fiber marginal is `uniformHashFibers_setSteering`: resampling the steering gate's fiber on
  top of `uniformHashFibers o` is `uniformHashFibers` of the outputs with the steering output
  replaced. With `shiftSteering_eq_setSteering` (`shiftSteering shift o = setSteering (o x7 0 +
  shift) o`) the simulated game's *two* samples (the honest fibers, then `uniformHashFiber
  wanted`) are the reference game's *one* sample at the shifted outputs — no extra cost.
* The freshness bridge costs nothing beyond the hop already charged: `programAll_eq_programIndices`
  needs (i) every request fresh against the log the steering sees, which is the bad event of the
  hop, and (ii) the requests to sit at **distinct indices**, which is a closed fact about the
  three hash slots / two pad slots (`steerRequests_distinct`), not a probabilistic one.
* **The stage-2 bound must defer the unread labels as one family, not one gate at a time.** The
  bad event is "some log entry hits the hidden set of **its own** gate's unselected label", so the
  union bound costs one label set per log **entry** (`k q / 2^128`). Bounding one gate at a time
  and summing over gates would cost `1270 k q / 2^128` and blow the budget. `setKeyLabels`
  replaces the selected label of every gate at once, so after the deferral each entry reads one
  coordinate of a uniform family (`map_labels_uniform`) — the accounting of §4 is unchanged.
  `secondStage_hidden_le`'s `unread` hypothesis (`game (setKeyLabels key values labels) = game
  key`) is what P9b must discharge for the two games: the released table ignores the label key
  (the secret oracles do not read labels), stage 1 never touches the key, and stage 2 sees only
  `Lamport.selectedLabels` and the programming at `selectedLabel`, all at the selected bit.
* `steerTo_eq_map` writes the `true` branch of the steering as a fiber sample it ignores
  (`PMF.map_const`), so both branches have the reference game's shape "sample a fiber, then
  program". P10 can therefore treat the two branches uniformly.

**Corrections from slice 3g.**

* The `unread` hypothesis of `secondStage_hidden_le` is **not** a property of a whole game: its
  `values : LabelIndex → Bool` is fixed, while the bits an input selects vary over the support of
  stage 1. It is a property of the **second stage with the input already fixed**
  (`hybridStageTwo`, `referenceStageTwo`, `simulatedStageTwo` all take `input` as a parameter and
  the key only inside `stageTwoState`). The stage-1 log is then a constant of the conditioning and
  the union bound still runs over the whole final log, as the accounting requires. P10 must apply
  the bound after the first stage is conditioned, using `firstStage_key_congr` (the key is
  independent of the first-stage outcome).
* `unread` holds for the **simulated** and the **reference** second stage, and trivially for the
  hybrid one, but the *hybrid table* does depend on the whole key: `BitAdaptor.garble` reads
  `hashToField` at the false label and `encrypt` at the true label, so both labels of every gate
  enter the released rows. Only the **reference** table is key-free (`Coordinates.table_key`: the
  secret oracles discard their label argument). This is why §4 bounds the bad events on the `R`
  side, and it is not optional: the hybrid-side statement would be false.
* `steer` factors as "sample a list of program requests, then program" (`steer_eq_map` through
  `steerRequestLaw`), and the request law reads the state only through the view and the table. With
  `programAll_view_congr` (programming reads only the view and the log) this gives
  `steer_visible_congr`, which is what makes the simulated second stage's `unread` a one-line
  consequence of `encodeAffine_setKeyLabels`.
* The accounting of §4 is now machine-checked, not only argued: `chainOneTime_lt` proves
  `2/p + 1270·p/2^384 + 6/2^128 < 2^-119` (the three one-time terms of §4: the mask law, the
  tensorised digest replacement, the freshness of the two chunks the steering reparametrisation
  swaps) and `workPerAdvantage_of_chain` instantiates `workPerAdvantage_of_le` at `K = 10` with the
  challenge's own `adversaryWork = firstQueryBudget + secondQueryBudget + 1`. So the only thing
  P10 still owes is the inequality `advantage H S ≤ 10 q / 2^128 + chainOneTime`.
* The first hop's algebra came out exactly as §4 step 1 claims. Garbling reads each gate at exactly
  two labels (`usedLabel`: the false label at the three hash slots, the true label at the two pad
  slots), so programming every index there to a fresh block makes the Davies--Meyer hash of the
  false label the concatenation of the three fresh chunks and the pad of the true label the
  concatenation of the two fresh chunks; the garbled table is then literally a `Coordinates.table`
  (`curveGarble_programFamily`). The fresh family is in bijection with one 384-bit digest and one
  256-bit pad per gate (`freshEquiv`), which is the interface `hashFibers_total_difference` of step
  2 consumes. **No constant moved.**

**Corrections from slice 3h.**

* **The one-time terms are paid TWICE, once per side of the chain.** §4 listed the mask
  replacement (`2/p`) and the tensorised digest replacement (`1270·p/2^384`) only under the `H`
  side's step 2, but the `S` side's step 7 also has to turn *its* reparametrisation's fresh
  secrets into `R(u)`'s uniform `Coordinates` plus fiber sample, which is the same pair of
  replacements. The chain reaches `S` only through `R(b)` (the hybrid-side bad bounds are
  unsound — see slice 3g), so there is no way to share them. `chainOneTime` is therefore now
  `sideOneTime + sideOneTime + 6/2^128` with `sideOneTime = 2/p + 1270·(p/2^384)`, and
  `chainOneTime_lt` is restated at `2^-118` (it was `2^-119`; the doubled value is `2566/2^130`
  and `2^-119 = 2048/2^130`, so the old bound was **false** for the doubled terms).
  `chainOneTime_le : chainOneTime ≤ 2^-101` and `workPerAdvantage_of_chain` are unchanged, so
  `K ≤ 10`, `ε₀ ≤ 2^-101` and the arithmetic tail still close the obligation.
* **`publicAnswer_programIndices_single` does not apply to the hops as §4 describes them.** Its
  `others : ∀ index' ≠ index, programs index' = none` hypothesis is false for a *family*
  programming, and both hops of step 3 program all 6350 indices at once. The right statement is
  per-query: a public query names exactly one fixed-key index, so only that index's own request
  matters (`publicAnswer_usedPrograms`, `publicAnswer_selectedPrograms`, both built on
  `publicAnswer_permutation_congr` + `programIndices_congr_at`). The hidden-set cardinality and
  hence the constant are unchanged.
* **An identical-until-bad hop of this chain needs a bad event over the *outcome*, not over the
  sample.** `advantage_bind_le_bad` charges `bad ⊆ Sample`, but each hop's bad event is "some
  entry of the log the differing stage produces is bad", and that log is part of the outcome.
  `advantage_bind_le_jointBad` (new, in `Proof/Chain.lean`) charges the bad mass under the joint
  law of the sample and the differing step's outcome; it specialises to `advantage_bind_le_bad`
  on the joint law, so nothing about the accounting changes.
* **The reference game's programming really is the first hop's programming, with no slack.** At a
  gate whose slot reads the *selected* label, `selectedPrograms` and `usedPrograms` are the same
  request (`selectedPrograms_selected`): at a `false` gate the hash slots both take the digest
  chunks, and at a `true` gate the pad slots both take `pads`, because the released row
  `pad ⊕ fieldBytes(slope + hash)` cancels against `fieldBytes` of the selected output
  `slope + hash`. At the other slots `selectedPrograms` is `none`, so the two views differ
  exactly at the *unselected* labels, which is what the second hop charges.
* **`hybridStageTwo`'s `unread` has to be re-proved for the state whose view is itself programmed
  at the selected labels** (`selectedStageTwo_unread`): the programming is a function of the key,
  and `selectedPrograms_setKeyLabels` is what makes it independent of the replaced labels. The
  slice-3g `hybridStageTwo_unread` alone is not enough.
* **`rw` cannot rewrite a lemma whose metavariable would capture a bound variable.** Rewriting
  `hybridData.bind ?continuation` under `fun key => …` fails with "did not find an occurrence"
  even though the pattern is visibly present. Go under the binder first with
  `congrArg (PMF.bind _) (funext fun key => ?_)` and rewrite at the top level. The same applies
  to every `bind`-splitting lemma of this file, which is why `bind_pairLaw` and `bind_stageLaw`
  are always applied with their continuation given **explicitly** (that makes the match
  first-order).

**Corrections from slice 3i.**

* **The missing tool of step 2 exists now, and §4's step 2 was otherwise accurate.**
  `hashFibers_total_difference` does **not** plug straight into the step, as slice 3h warned:
  `R(b)` samples `uniformHashFibers o` at the *selected* outputs while the digest family reduces
  to `raw.hash`, and the two differ at every gate whose input bit is `true`. The general tool is
  `productPMF_bind_congr` (`Proof/Product.lean`): two product laws that agree off a finite set of
  coordinates give the same game to a continuation that never reads those coordinates. It is a
  `Finset` induction on `productPMF_bind_update_congr`, exactly as predicted, and the gate-level
  instance is `uniformHashFibers_bind_congr` (`Proof/GateProduct.lean`) with `setGate` for the
  one-coordinate update. The three pieces (a), (b), (c) of the old plan all landed as written.
* **The order of the three pieces is forced.** The fiber sample must be deferred past the first
  stage (`PMF.bind_comm`) *before* the marginal lemma can be applied, because the selected
  outputs `(encodeCoordinates input raw).hash` are a function of the input the first stage
  chooses. Inside the deferral the input is a constant, and the changed set is exactly
  `{gate | inputBits input gate = true}`.
* **The invariance side of the marginal lemma is an equality with no slack**
  (`selectedPrograms_setGate`): at a gate whose bit is `true` the hash slots of
  `selectedPrograms` are `none` and the pad slots read only the row and the selected output, so
  the whole second stage is literally unchanged by resampling that gate's fiber. This was the
  last place the architecture could have been wrong on the `H` side. It is not wrong.
* **Reordering samples is cheap if both sides are fused first.** Both games of step 2 are towers
  of independent uniform binds in different orders. Do **not** commute them one at a time:
  `simp only [uniformOfFintype_bind_prod]` collapses a right-nested tower into a single uniform
  sample of the product in one step, and `uniformOfFintype_bind_bijection` then transports one
  side to the other along a single explicit `Equiv` whose `left_inv`/`right_inv` are `rfl` after
  `rintro`. `hybridData_eq_uniform`, `digestedSampleEquiv` and `referenceSampleEquiv` are the
  three instances; the `S` slice should do the same rather than chain `PMF.bind_comm` under
  binders.
* **No constant moved.** Step 2 cost exactly `2/p + 1270·(p/2^384) = sideOneTime`, which is what
  §4 and `Proof/Chain.lean` already budgeted for one side.

**What P10 still has to do.** The whole `H` side is done: steps 1 and 3 (slice 3h,
`Proof/HybridChain.lean`) and step 2 plus the identification with `R(c/s)` (slice 3i,
`Proof/HybridReference.lean`). In order, what is left:

(i) **`S` side, steps 4–6**: the same three hops for the simulated game, with `steer_eq_map` /
`programAll_steerRequests` for the steering. `advantage_firstView_le` and `advantage_secondView_le`
are stated generically in the key-free data `Data`, so they are reusable verbatim provided the
`S` side's first stage is put in the same `loggedFirstStage … (circuit datum) (view datum)` shape.

(ii) **`S` side, step 2's twin**: the `S` side must pay its own `sideOneTime`. The whole of
`Proof/HybridReference.lean` after `digestedReference_eq` is generic in the bridge key in
everything but name — `referenceRound`, `referenceGame_eq`, `referenceGame_eq_split`,
`referenceSampleEquiv`, `digestField_of_mem_uniformHashFibers`, `selectedPrograms_setGate`,
`selectedStageTwo_setGate` and `uniformHashFibers_selected` are already stated for an arbitrary
`bridge : NonZeroBase → BaseField` or with no bridge key at all. Only `digestedBody`,
`fiberedBody`, `referenceCircuit` and the four games are specialised to `(mulScalar scalar).symm`;
the `S` slice should generalise those four definitions over the bridge key rather than duplicate
them.

(iii) **step 7** via `twoStageGame_congr`, `visibleCoordinates_offCurve` / `visibleCoordinates_onCurve`,
`steer_programSelected`, `programIndices_steerPrograms` and `uniformHashFibers_setSteering`.

(iv) chain with `advantage_trans` and close with `workPerAdvantage_of_chain`.

**The constant assignment (slice 3h, updated slice 3i).** The budget is
`10·(q₁+q₂)/2^128 + chainOneTime`, `chainOneTime = sideOneTime + sideOneTime + 6/2^128`,
`sideOneTime = 2/p + 1270·(p/2^384)`. **No constant moved in slice 3i.**

| step | which side | per-query | one-time | status |
|---|---|---|---|---|
| 1 (reparametrise `π`) | H | 0 | 0 | **done** (`hybridGame_eq_fresh`) |
| 3, hop A (stage 1 → `π°`) | H | `2q₁/2^128 ≤ 2q/2^128` | 0 | **done** (`advantage_firstView_le`) |
| 3, hop B (stage 2 → selected labels) | H | `2q/2^128` | 0 | **done** (`advantage_secondView_le`) |
| 2 (mask `F*→F`) | H | 0 | `2/p` | **done** (`advantage_digestedGame_maskedGame_le`) |
| 2 (1270 digests → field + fiber) | H | 0 | `1270·p/2^384` | **done** (`advantage_maskedGame_fiberedDigestGame_le`) |
| 2 (fiber sample → selected outputs) | H | 0 | 0 | **done** (`fiberedDigestGame_eq_fiberGame`) |
| 2 (identify with `R(c/s)`) | H | 0 | 0 | **done** (`fiberGame_eq_referenceGame`) |
| 4 (reparametrise `π`) | S | 0 | 0 | open |
| 5 (stage 1 → `π°`) | S | `2q/2^128` | 0 | open |
| 6 (stage 2 unselected) | S | `2q/2^128` | 0 | open |
| 7 (`swap(r₁,r₂)` reparametrisation) | S | `2q/2^128` | `6/2^128` | open |
| 7 (mask and digests of the `S` side) | S | 0 | `sideOneTime` | open |

Slice 3h consumed `4·(q₁+q₂)/2^128` of the per-query budget and none of the one-time budget.
**Slice 3i consumed exactly one `sideOneTime` of the one-time budget and none of the per-query
budget.** Together the `H` side costs `4·(q₁+q₂)/2^128 + sideOneTime`
(`advantage_hybridGame_referenceGame_le`). What is left for the `S` side is
`6·(q₁+q₂)/2^128 + sideOneTime + 6/2^128`, and the two shares sum to exactly
`10·(q₁+q₂)/2^128 + chainOneTime`. The `S` side's share is untouched.

Two things the slice-3b analysis had that this chain does **not** need: hiding all 1270
unselected-label values by an explicit shift (absorbed by `P4`), and the `(2^128 − q)`
denominators (the `R`-side bounds sample the hidden label fresh, so each log entry hits with
probability exactly `k/2^128`).

## 5. Lemma list, dependencies, status

| id | content | file / name | status |
|---|---|---|---|
| P1 | programming involution `(π, r) ↦ (π programmed at ℓ to r, π ℓ)`; uniform `π` = uniform `π°` programmed at fresh uniform `r`; family version over `FixedKeyIndex` | `Proof/Programming.lean`: `programAt`, `programAtEquiv`, `uniform_programAt`, `programFamily`, `uniform_programFamily` | **done** |
| P2 | deterministic identical-until-bad for logged runs: same log, views agreeing off `bad` ⇒ same `(result, log)` law on good logs; bind form of `identical_until_bad`; log monotone, log length ≤ initial + budget | `Proof/Logged.lean`: `run_idealOracle_agree`, `bind_identical_until_bad`, `run_idealOracle_log_mono`, `run_idealOracle_log_length` | **done** |
| P3 | independence bad-bounds: union bound over a log (`hidden_label_bound`); one label of a uniform key is a uniform block (`setKeyLabel` involution, `map_keyLabel_uniform`, `uniform_keyLabel_mem`); hidden sets of one programmed permutation, 2 per direction (`forwardHidden`, `inverseHidden`, `hiddenLabels_card`, `publicAnswer_programIndices_single`); stage-1 bound with the key sampled up front (`firstStage_key_deferred`, `firstStage_hidden_le`); stage-2 bound with the key read only through the selected labels: replacing one label of **every** gate at once is an involution of the key (`setKeyLabels`, `keyLabels`, `swapKeyLabels`, `uniform_bind_setKeyLabels`), one label of a uniform family is a uniform block (`uniform_bind_update_labels`, `map_labels_uniform`, `uniform_labels_mem`), and `secondStage_hidden_le` deferres the whole unread family so the union bound runs over the log entries | `Proof/Hidden.lean`, `Proof/SecondStage.lean` | **done** |
| P4 | static bijection raw ↔ middle; `c0` affine in `mask`; visible law uniform off-curve, shift law on-curve | `Proof/Reference.lean`: `middleEquiv`, `Coordinates.table_c0_eq`, `visibleCoordinates_offCurve`, `visibleCoordinates_onCurve` | **done** |
| P5 | deferred sampling: transfer form `twoStageGame_congr` (equal joint laws of `(view, rest r)` per first-stage result ⇒ equal games) and factored form `twoStageGame_eq_deferredGame`; both by `tsum_map_mul` + `ENNReal.tsum_comm` | `Proof/Deferred.lean`: `twoStageGame`, `deferredGame`, `twoStageGame_apply`, `twoStageGame_congr`, `twoStageGame_eq_deferredGame`, `map_view_of_joint` | **done** |
| P6 | TV facts: total difference `∑ |law₁ − law₂|` with triangle inequality and both bind sub-additivities (`bind_apply_sub_le` swaps the sampled law, `bind_apply_sub_le_of_le` swaps the continuation); `U(F*)` vs `U(F)` total difference `2/p`; one 384-bit digest vs (`U(F)` then `uniformHashFiber`) total difference `≤ p/2^384` (fiber sizes are within one residue block of `2^384/p`, by the two injections `fiberElement`/`fiberIndex`); **tensorisation**: the law of independent coordinates on a finite function type, its uniform / bind / one-coordinate-resampling laws, the uniform law of a coordinatewise subtype as a product, and `totalDifference (⊗ first) (⊗ second) ≤ ∑ coordinates`; instantiated at the 1270 gates: `1270 · p/2^384` for the whole digest family | `Proof/Distance.lean`: `totalDifference`, `totalDifference_triangle`, `bind_apply_sub_le`, `bind_apply_sub_le_of_le`, `mask_total_difference`, `card_hashFiber_lower`/`_upper`, `count_mul_difference_le`, `hashFiber_total_difference`; `Proof/Product.lean`: `productPMF`, `productPMF_apply`, `uniformOfFintype_pi`, `productPMF_bind`, `productPMF_bind_update`, `uniform_subtypePi_map_val`, `totalDifference_productPMF_update`, `totalDifference_productPMF`, `map_equiv_apply`, `uniformOfFintype_map_bijection`, `totalDifference_map_bijection`; `Proof/GateProduct.lean`: `Gate`, `gateCurry`, `gateProduct`, `card_gate`, `uniformOfFintype_gateValues`, `uniformHashFibers_eq_gateProduct`, `hashFibers_total_difference`; **the marginal lemma** (slice 3i): `productPMF_bind_update_congr`, `productPMF_bind_congr`, `setGate`, `setGate_gateCurry`, `uniformHashFibers_bind_congr` | **done** |
| P7 | `steer` in deferred form: the programmed reference view releases every selected output and hence `bridgeKey + mask·curveGap`, so on-curve `current = u` and `wanted = o x7 0 + (c/s − u)` — the steering is `shiftMiddle (c/s − u)` on the visible data; the double programming (honest, then steered) of the steering gate is `R`'s single programming of the shifted outputs on `π° ↦ swap(honest range, steered range) ∘ π°` ; the simulator's skip-if-logged `programAll` is the unconditional `programIndices` whenever every request is fresh (the hop's bad event) and the requests sit at distinct indices; resampling the steering gate's fiber on the reference fiber law is the reference fiber law of the shifted outputs | `Proof/DeferredSteering.lean`: `swap_trans_swap`, `programmed_programmed`, `programIndices_programIndices`, `hashToField_programSelected`, `decrypt_programSelected`, `evaluate_programSelected`, `curveEvaluate_programSelected`, `steerTo`, `steer_programSelected`, `steerPrograms`, `programIndices_steerPrograms`; `Proof/FreshBridge.lean`: `programsOfRequests`, `programIndices_programPermutation`, `programAll_eq_programIndices`, `steerRequests`, `steerTo_eq_map`, `steerRequests_distinct`, `programsOfRequests_steerRequests`, `programAll_steerRequests`; `Proof/GateProduct.lean`: `setSteering_gateCurry`, `uniformHashFibers_setSteering`, `shiftSteering_eq_setSteering` | **done** |
| P8 | arithmetic tail `ε ≤ K q/2^128 + ε₀`, `K ≤ 2^28`, `ε₀ ≤ 2^-101` ⇒ `WorkPerAdvantage 100 (q+1) ε`; `advantage ≤ 1` | `Proof/Reference.lean`: `workPerAdvantage_of_le`, `advantage_le_one` | **done** |
| P9a | `R(b)` as a `PMF Bool`: `programIndices` (unconditional partial programming), `gateKey`/`selectedLabel`/`slotRange`/`tableRow`, `selectedPrograms`, `HashFibers`/`uniformHashFibers`, `programSelected`, `referenceStage2`, `referenceGame`; `run_idealOracle_support` (a run changes only the log); `selectedPrograms_hash`/`_pad`/`_label` | `Proof/ReferenceGame.lean` | **done** |
| P9b | unfold `idealGame` for `hybridSimulator` and `simulator` into the shape of §4, marginalize unused tape fields, and discharge the `unread` hypothesis of `secondStage_hidden_le` for every second stage: the labels one input leaves unselected (`unreadLabelBits`) are read by no game, because `encodeAffine`, `selectedLabel` and `selectedPrograms` read only the selected label, the reference table ignores the key entirely, and an ideal-oracle run reads only the view and the log | `Proof/GameShape.lean`: `inputLabelBits`, `unreadLabelBits`, `keyLabel_setKeyLabels_of_ne`, `selectedLabel_setKeyLabels`, `encodeAffine_setKeyLabels`, `Coordinates.table_key`, `firstStage_key_congr`, `map_fst_run_congr`, `programAll_view_congr`, `steerRequestLaw`, `steer_eq_map`, `steer_visible_congr`, `stageTwoState`, `decisionLaw`, `bind_decisionLaw`, `hybridStageTwo`/`_unread`, `referenceStageTwo`/`_unread`, `simulatedStageTwo`/`_unread`, `setCurve`, `uniform_bind_setCurve`, `setOracle`, `uniform_bind_setOracle`, `simulatedGame_eq`; `Proof/Privacy.lean`: `hybridGame_eq` | **done** |
| P10 | assemble §4 with `advantageTriangle` / `event_difference_le` and P8 | assembly layer `Proof/Chain.lean`: `advantage_bind_le_bad`, `advantage_bind_le_jointBad`, `advantage_bind_le_totalDifference`, `advantage_bind_le_of_le`, `advantage_trans`, `sideOneTime`, `chainOneTime`, `chainOneTime_lt`, `workPerAdvantage_of_chain`; first hop's algebra `Proof/Reparametrise.lean`: `usedLabel`, `programFamily_apply`, `freshDigest`/`freshPad`/`freshHash`, `curveGarble_programFamily`, `freshEquiv`, `uniform_map_freshEquiv`; `H`-side steps 1 and 3 `Proof/HybridChain.lean`: `setKey`/`uniform_bind_setKey`, `hybridTwoStage`, `hybridOn`, `hybridGame_eq_hybridOn`, `hybridGame_eq_split`, `freshValue`, `usedPrograms`, `programFamily_eq_programIndices`, `uniform_bind_usedPrograms`, `hybridFresh`, `hybridGame_eq_fresh`, `queryLabelIndex`, `usedHidden`, `UsedBad`, `usedLabel_eq_keyLabel`, `publicAnswer_usedPrograms`, `bind_pairLaw`, `advantage_firstView_le`, `publicAnswer_permutation_congr`, `programIndices_congr_at`, `digestedRaw`, `selectedPrograms_selected`/`_unselected`, `unreadQueryIndex`, `SelectedBad`, `publicAnswer_selectedPrograms`, `selectedStageTwo`/`_unread`/`_length`, `usedStageTwo`/`_agree`, `bind_stageLaw`, `secondBad`, `secondBad_mass_le`, `advantage_secondView_le`, `hybridData`, `digestedReference`, `advantage_hybridGame_digestedReference_le`; `H`-side step 2 and the `R` identification `Proof/HybridReference.lean`: `uniformOfFintype_bind_bijection`, `hybridData_eq_uniform`, `ReferenceDatum` with its projections, `referenceRaw`, `referenceCircuit`, `digestedBody`, `fiberedBody`, `referenceOf`, `hybridCircuit_eq_referenceCircuit`, `digestedGame`, `digestedSampleEquiv`, `digestedReference_eq`, `maskedGame`, `advantage_digestedGame_maskedGame_le`, `fiberedDigestGame`, `advantage_maskedGame_fiberedDigestGame_le`, `digestField_of_mem_uniformHashFibers`, `selectedPrograms_setGate`, `selectedStageTwo_setGate`, `uniformHashFibers_selected`, `fiberGame`, `fiberedDigestGame_eq_fiberGame`, `referenceRound`, `referenceGame_eq`, `referenceGame_eq_split`, `referenceSampleEquiv`, `fiberGame_eq_referenceGame`, `advantage_digestedReference_referenceGame_le`, `advantage_hybridGame_referenceGame_le` | **open** (the whole `H` side is done; the whole `S` side and the final assembly are not) |

The assembly layer of P10 lives in `Proof/Chain.lean` and `Proof/Reparametrise.lean`; the game
shapes and the `unread` discharges live in `Proof/GameShape.lean`.

Dependencies: P9a needs P4's definitions; P3's stage-1 half needs P2 (log length) and P9a, its
stage-2 half needs P6's product laws (`Proof/SecondStage.lean` imports `Proof/Product.lean`); P5 needs P4; P7 needs
P1 and P9a; P10 needs everything. Slice 3d also added `Adversary`/`Selected` abbreviations,
`firstState`/`loggedFirstStage` (the stage-1 run in logged, key-free form; `map_loggedOutcome_congr`
shows a logged run depends only on the view and the initial log) and `slotBit`/`queryIndex`. Generic helpers are in `Proof/Uniform.lean`
(`uniformOfFintype_bind_equiv`, `uniformOfFintype_bind_prod`, `uniformOfFintype_map_equiv`,
`bind_congr_support`).

## 6. Practical notes for the next slice

* `congr 1`, `rfl`, and `simp` on terms containing `BaseField` arithmetic can hit
  `maximum recursion depth` (ZMod numerals). Use `Coordinates.ext ?_ ?_ …` with
  `dsimp only [...]` per field, `change` to the explicit form, then `rw`/`ring`
  (see `releaseEquiv`, `offsetTerm_releaseMiddle`).
* `Fintype (BitVec 256)` is declared in `Proof/Reference.lean`; `Fintype (BitVec 384)` in
  `Proof/Simulator.lean`; `Fintype Coordinates` via `Coordinates.data`.
* The `sorry` must remain the one at `hybridGame_close_to_idealGame` until P10 replaces it.
* `exact inductionHypothesis _ _ member` in an induction over `OracleProgram` can time out at
  `whnf` when the expected type fixes the state by unification before `member` is seen (it then
  unfolds `run`); pass the state explicitly, as in `run_idealOracle_support`.
* `public` is a keyword; name the public value `circuit`. `Nonempty InputMacKey` is declared in
  `Proof/Hidden.lean`.
* Chunk convention for a 384-bit hash / 256-bit pad at slot `j`: `extractLsb' (128 * j) 128`
  (`slotRange`), matching `hashRequests`/`padRequests`.
* `field_simp` and `ring` loop or hit `maximum recursion depth` on the numeral `2 ^ 384`. Prove the
  arithmetic on abstract reals first (`count_mul_difference_le`) and instantiate afterwards.
* `rw` will not see through a definitional unfolding such as `tableRows table .x3 = table.x3` or
  `gateMac mac .x3 = mac.x`. Use `set` for the long programmed-oracle term and state one `have`
  per adaptor in the syntactic form the goal has; the defeq proof term still typechecks
  (`curveEvaluate_programSelected`).
* `PermutationOracle` has no `ext` lemma; close an oracle equality with
  `congrArg PermutationOracle.mk (funext …)`.
* Applying a product lemma whose statement mentions `PMF.uniformOfFintype` on a **subtype of a
  function type** directly against an expected type hits `maximum recursion depth`: the expected
  type fixes the `Fintype` instances first and unification unfolds `Fintype (BitVec 384)`, which
  tries to evaluate `2 ^ 384`. Elaborate it without an expected type first
  (`have base := uniform_subtypePi_map_val …`) and then `exact base` / assign it to a typed
  `have`; the defeq check afterwards is cheap. The same trick fixes the analogous failure for a
  whole-term `rfl` between two `PMF.map`s: state the function equality as a separate
  `funext … rfl` and `rw` it instead.
* `decide` refuses a goal that still mentions free variables even when the decidable part is
  closed (e.g. `List.Pairwise (·.index ≠ ·.index) [⟨i₀, label, range₀⟩, …]`). `simp only` the
  list structure away first (`List.pairwise_cons`, `List.mem_cons`, `forall_eq`, `false_implies`,
  `implies_true`) so that only the closed index inequalities remain, then `decide`.
* `omit [inst] in` must come **before** the doc comment of the declaration it modifies, not
  between the doc comment and the `theorem` keyword.
* **`rfl` between two projections of one `def` applied to different arguments can hit
  `maximum recursion depth`.** `(stageTwoState view log table carrier k₁).log =
  (stageTwoState view log table carrier k₂).log` is iota-trivial, but unification tries congruence
  first and then has to decide `k₁ =?= k₂`, which unfolds `setKeyLabels` into a `Vector.ofFn` over
  254 positions. State one-sided projection lemmas (`stageTwoState_view`, `stageTwoState_log`, …,
  each `:= rfl`) and `rw` with them; the one-sided `rfl` reduces the left side and never compares
  the arguments.
* `PMF.map_pure` does not exist; the name is `PMF.pure_map`. `div_le_div_iff` is now
  `div_le_div_iff₀`. `congrArg` on a `PMF.map` must abstract the **function** argument
  (`congrArg (fun step => PMF.map step law)`), since `PMF.map` takes the function first.
* `ring` cannot prove `2 ^ 254 * 2 ^ 130 = 1 * 2 ^ 384`: it normalises the numerals and compares
  116-digit integers. Use `rw [one_mul, ← pow_add]`.
* After `fin_cases chunk` the goal keeps `128 * 0` and `FixedKeySlot.hash ⟨0, ⋯⟩`; `simp only`
  with the extraction lemmas does not fire. Plain `simp` with the same lemmas does.
* **`rw` silently refuses to rewrite under a binder when the instantiation captures the bound
  variable.** `rw [hybridData_bind]` on `(uniform key).bind fun key => hybridData.bind (body key)`
  reports "did not find an occurrence of the pattern `hybridData.bind ?continuation`" while
  printing a target that visibly contains it. Descend with
  `refine congrArg (PMF.bind _) (funext fun key => ?_)` first.
* A `bind`-splitting lemma such as `bind_pairLaw` / `bind_stageLaw` must be applied with its
  continuation **given explicitly**: the pattern `?continuation ((key, datum), outcome)` is not a
  Miller pattern, so `rw` cannot solve it, but supplying the lambda makes the match first-order.
  `rw` does beta-reduce and project the supplied lambda against the explicit pair, so
  `fun sample => f sample.1.2 sample.2.1.1` matches `f datum outcome.1.1` after instantiation.
* Passing `_` for the two `State` arguments of `run_idealOracle_agree` makes its `agree`
  hypothesis elaborate against `publicAnswer (State.view ?m) query = publicAnswer (State.view ?m)
  query` and fail; give both states explicitly (and `show` the goal in `map loggedOutcome` form
  first).
* `ENNReal.toReal_ofNat` rewrites **all** occurrences of `(2 : ENNReal).toReal` at once, so a
  second copy of it in the same `rw` list fails with "did not find an occurrence".
* `simp only […, BitAdaptor.encode]` leaves `if True then … else …` behind when the bit has
  already been rewritten to `true`; plain `simp` closes it.
* **`Bool.eq_false_or_eq_true b` is `b = true ∨ b = false`** — `true` first, despite the name.
  Prefer `cases set : inputBits … with | true => … | false => …`, which also substitutes the
  constructor into the goal, or `by_cases set : … = true` followed by `simpa using set`.
* **`PMF.bind_map`'s `g ∘ f` will not unify against an explicit lambda through `rw`/`show` with
  metavariables.** Build the equation as a `have` with the law, the map function and the
  continuation all given explicitly and chain it with `.trans`; the defeq check between
  `Function.comp g f` and `fun x => g (f x)` is then cheap and never has to be guessed.
* **`initialState tape table carrier` and `firstState (Garbling.evaluationOracle tape) table
  carrier tape.inputMacKey` are definitionally equal but not syntactically**, so
  `map_loggedOutcome_firstState` does not fire on a run started from `initialState`. Insert
  `rw [show initialState … = firstState … from rfl]` first.
* **`simp only [uniformOfFintype_bind_prod]` fuses a whole right-nested tower of independent
  uniform binds into one uniform sample of the product** in a single call, even though the lemma
  is higher-order. This is the cheap way to reorder samples: fuse both sides, then transport
  along one `Equiv` with `uniformOfFintype_bind_bijection` and close with `rfl`. A cascade of
  `PMF.bind_comm` under binders is several times the work and hits the binder-capture problem
  above.
