# Proof architecture for `hybridGame_close_to_idealGame`

Status of the tree (after slice 3n): every obligation is proved except the single `sorry` at
`Proof/Privacy.lean`, theorem `hybridGame_close_to_idealGame` (statement must stay
byte-identical). Both sides of the chain reach a reference game, **the final assembly is
machine-checked** (`workPerAdvantage_of_steering`, `Proof/Assembly.lean`), and the only
remaining input is the steering hop -- step 7 -- as a single named inequality between two
explicit games. This document is the plan for closing it, the pieces that are already
machine-checked, and the constant it produces. The next slice must inherit it rather than
re-derive it.

Slice 3n built the **glue that makes the lazy-sampling theorem usable on the hop's two
games** (`Proof/Erased.lean`) and answered the shape question slice 3m flagged. See
"Corrections from slice 3n"; the headline is that one tracked index suffices but the
union bound must be keyed to each log entry's own index, and that `compatibleLaw_run`
alone does not apply to either game because both run their second stage on a
*programmed* view. `hybridGame_close_to_idealGame` still carries the single `sorry` and
no constant moved.

Slice 3m built the **lazy-sampling theorem for one fixed-key permutation** (`Proof/Lazy.lean`),
which is the tool the oracle half of step 7 was missing. It is `sorryAx`-free and self-contained:
a partial injective assignment, the lazy handler, the run-level eager-to-lazy equivalence, and
the conditional-uniformity corollary with its `1 / (2 ^ 128 - q)` charge. See "Corrections from
slice 3m". `hybridGame_close_to_idealGame` still carries the single `sorry` and no constant
moved.

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
`Proof/GateProduct.lean`). At that point the whole `S` side (steps 4–7) and the final
assembly were still open.

Slice 3j closed **steps 4, 5 and 6 of the `S` side and the `S` side's own copy of step 2**
(`Proof/SimulatedChain.lean`, `Proof/SimulatedReference.lean`), so the simulated side is now
machine-checked up to the steering identification:

```lean
theorem advantage_simulatedGame_steeredReferenceGame_le :
    advantage (idealGame … simulator …)
        ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
          steeredReferenceGame (fun _ => bridgeKey.value) scalar …)
      ≤ 4 * (q₁ + q₂) / 2 ^ 128 + sideOneTime
```

`steeredReferenceGame bridge` is `R(bridge)` with the simulator's second stage — the honest
labels and then `steer` — in place of the reference game's, written in the split sample shape
`referenceGame_eq_split` puts `referenceGame` into. The whole of step 2 was reused rather
than rewritten: `referenceCircuit`, `digestedBody`, `fiberedBody` and the four games were
generalised over `bridge : NonZeroBase → BaseField`, `uniformHashFibers_selected` over the
second stage on the programmed state, and hop B over the pair of second stages
(`advantage_secondStage_le`). **Only step 7 and the final assembly are open**, so
`hybridGame_close_to_idealGame` still carries the single `sorry`. See "What P10 still has to
do" and the constant assignment below.

Slice 3k built the two-stage glue and the visible joint laws that step 7 consumes
(`Proof/VisibleGame.lean`), the off-curve half of the steering identification, and a
reparametrisation tool for a doubly programmed permutation (`Proof/Retarget.lean`). It did
**not** close step 7: §4's step 7 is **not provable with the tools the tree has**, and the
obstruction is a real gap in the plan rather than a missing lemma. It is analysed in full
under "Corrections from slice 3k" below, together with the tool that would close it and the
`K` decision that closing it forces. `hybridGame_close_to_idealGame` still carries the
single `sorry`, and no constant was moved.

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

**Superseded in slice 3l: `K` is `16`, not `10`.** Step 7's bad points do not live on a
deferrable label, so its charge is `8 q / 2^128`, not `2 q / 2^128`. See `chainPerQuery` in
`Proof/Chain.lean` and "Corrections from slice 3l". `ε₀ = chainOneTime` did not move.

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

**Corrections from slice 3j.**

* **Slice 3i's reuse prediction was right, and the reusable surface is larger than it
  said.** Generalising `referenceCircuit`, `digestedBody`, `fiberedBody` and the four games
  over `bridge : NonZeroBase → BaseField` took one edit and one green build. But the `S`
  side also needed the *second stage* abstracted, in two places, and both were cheap:
  `uniformHashFibers_selected` now takes the second stage on the programmed state (its
  invariance step is `programSelected_setGate`, not `selectedStageTwo_setGate`), and hop B is
  now `advantage_secondStage_le`, generic in the pair of second stages with the
  `agree`/`unread`/`length` hypotheses; `advantage_secondView_le` is its `H`-side
  instantiation. With those three generalisations the `S` side's step 2 needed no new
  probabilistic argument at all.
* **§4's step 6 is not a corollary of the `H` side's hop B, and its parenthesis —
  "`steer` reads only selected-label slots, so it is unaffected" — hides the only genuinely
  new work of the `S` side.** `steer` both *reads* and *writes* the view, and each half needs
  its own lemma.
  * Reading: `current` is the curve evaluation on the honest labels and `position` is the
    steering gate's evaluation, so the hop must know that evaluation touches the fixed-key
    oracle only at the *selected* label of each gate and only at the slots that label
    belongs to (the three hash slots at a `false` bit, the two pad slots at a `true` bit).
    That is `curveEvaluate_congr`, built from `hashBytes_congr`, `padBytes_congr`,
    `bitEvaluate_congr` and `evaluateDigit_congr`.
  * Writing: `programAll` must preserve the agreement of the two views. This is **not**
    automatic. `programIfFresh`'s freshness test reads `π⁻¹(range)` as well as `π(label)`,
    so two views that merely agree *at the selected label* could take different branches.
    They do not, because the steering's request indices are exactly the indices where
    `usedPrograms` and `selectedPrograms` are the same request (`selectedPrograms_selected`
    at a slot whose bit is the input's), hence where the two views agree as whole
    permutations. `programAll_congr_at`, `programAll_untouched` and
    `publicAnswer_programAll_congr` carry that through the request list.
* **The `S` side's bad event is the `H` side's `SelectedBad`, unchanged.** The steering
  contributes no bad event to steps 4–6: every step of the argument above is an equality.
  Step 7's `swap(r₁, r₂)` reparametrisation still owns the `6/2^128` freshness term. **No
  constant moved.**
* **`R(u)`'s bridge key is not a function of the carrier**, so the `S` side's target is
  `(uniform NonZeroBase).bind fun u => steeredReferenceGame (fun _ => u.value) …`, with the
  `u` sample bound outside the game. `steeredReferenceGame` is defined in the split sample
  shape (tape, key, oracle, carrier, raw) — the shape `referenceGame_eq_split` produces — so
  step 7 can compare `steeredReferenceRound (fun _ => u.value)` with
  `referenceRound (hybridBridge scalar)` under one sample without re-deriving either side.
* **`hybridBridge scalar`** is now the name of `fun carrier => ((mulScalar scalar).symm
  carrier).value`; `advantage_hybridGame_referenceGame_le` reads
  `referenceGame (hybridBridge scalar) …` (definitionally the old spelling).

**Corrections from slice 3k — READ THIS BEFORE TOUCHING STEP 7.**

* **§4's step 7 is not provable where it is scheduled, and its parenthesis "2 more hidden
  points per direction at those five indices, *stage 1 only*" is wrong as stated.** The
  double programming of the steering gate is, at one steering index with selected label
  `ℓ`, honest range `f` and steered range `s`,

  ```
  A = programmed (programmed π ℓ f) ℓ s        (the steered reference game)
  B = programmed π ℓ s                          (the reference game R(c/s))
  ```

  Writing `ρ = π ℓ`, the two differ exactly at: forward queries `x ∈ {π⁻¹ f, π⁻¹ s}` and
  inverse queries `y ∈ {ρ, f}` — two points per direction, as §4 says. Every one of the
  four is a condition on the **key label** `ℓ` (`ℓ = f' ⊕ π x`, `ℓ = s' ⊕ π x`,
  `ℓ = π⁻¹ y`, `ℓ = f' ⊕ y`, where `f = f' ⊕ ℓ` and `s = s' ⊕ ℓ` are the chunk values).
  But **`ℓ` is handed to the adversary by the second stage**, so neither
  `firstStage_hidden_le` (key independent of stage 1) nor `secondStage_hidden_le` (defers
  only the *unread* label of each gate) can bound it, and the hop as available is a
  **stage-2** hop whose bad event covers stage-2 queries.
* **The reparametrisation that would make it a stage-1 hop is circular.** `A` and `B` are
  exact reparametrisations of one another: with `σ` the stage-2 view and `ρ` the erased
  image, both games are `[σ uniform on the permutations sending ℓ to s] ⊗ [ρ uniform]`,
  with identical stage-2 views and stage-1 views differing by a 3-cycle on `{f, s, ρ}`.
  That is exactly §4's "stage 1 only". It cannot be used, because the substitution needs
  the swap data — hence `f`, `s`, hence the *input* — to be fixed **before** the first
  stage, and the input is the first stage's own output. The same circularity kills
  `programIndices_steerPrograms`'s `swapRanges` and the `twoStageGame_congr` route (the
  joint law would have to equate `(oracle, retargeted oracle)` with `(oracle, oracle)`).
* **What the remaining bad event really needs is permutation randomness, which the tree
  does not have.** Off the four bad points, two need the adversary to invert the
  unprogrammed `π` at a point it has not queried (`π⁻¹ f`, `π⁻¹ s`, and `ρ = π ℓ`), and
  one needs it to guess the discarded honest chunk `f'`. `f'` is a 128-bit chunk of
  `uniformHashFiber (o x7 0)`, whose largest point mass is about `1.11 / 2^128` — already
  above the `1/2^128` the accounting assumes — so even the chunk-freshness half does not
  fit the frozen `2 q / 2^128`. §4's note "the `R`-side bounds sample the hidden label
  fresh, so each log entry hits with probability exactly `k/2^128`" does not apply to this
  hop.
* **Moving the hop earlier does not help, and this was checked.** Doing the steering
  removal right after step 4 makes the honest range `chunk(digests) ⊕ usedLabel key index`
  with `digests` *marginally* uniform, but the released table is a function of
  `digestField digests`, so conditionally on what the adversary sees the digest is uniform
  only **in the fiber of a visible field element** — exactly the same conditional law as
  after step 2. And the steered range still depends on `wanted = o x7 0 + δ`, hence on the
  adaptively chosen input, so the circularity above is not removed either. The merge §4
  contemplated ("merging it into step 5") therefore buys nothing.
* **The ingredient step 7 actually needs is a random-permutation bound, and the challenge
  library already has its counting core.** Three of the four bad points
  (`π⁻¹ f`, `π⁻¹ s`, `ρ = π ℓ`) are hit only by a query that inverts or evaluates the
  *unprogrammed* permutation at a point the adversary has not pinned; conditionally on the
  whole transcript each is uniform over at least `2^128 - q` values. That is a lazy-sampling
  statement, and `formal/Cryptography/Permutation.lean` supplies its counting core:
  `compatiblePermutation_count` / `compatiblePermutation_mass` (the mass of the
  permutations compatible with a partial assignment is a factorial ratio),
  `injectiveAssignment_mass`, and `programCompatiblePermutation_uniform` (programming a
  fresh point of a compatible permutation is again uniform). Building the adaptive-run
  conditional-uniformity lemma on top of these is the work step 7 still owes; nothing in
  `Proof/` currently does it, which is why every existing hop is bounded on a *label*
  instead.
* **The fourth bad point (`y = f`, i.e. guessing the discarded honest chunk) needs a mass
  bound for one 128-bit chunk of `uniformHashFiber v`.** Its largest point mass is about
  `1.11 / 2^128` (the fiber has about `2^384 / p ≈ 1.35 · 2^130` elements and a fixed chunk
  value is taken by at most about six of them), so it is **not** `1/2^128`.
* **Consequence for the accounting.** With `1/(2^128 - q)` denominators for three points
  and `≈ 1.11/2^128` for the fourth, the honest charge for this hop is above
  `2 q / 2^128`. `workPerAdvantage_of_le` tolerates any `K ≤ 2^28`, so the chain still
  closes comfortably at, say, `K = 12` or `K = 16`; but `workPerAdvantage_of_chain` is
  stated at exactly `K = 10` and `Proof/Chain.lean` is frozen, so **closing step 7 will
  require the driver to re-open `Proof/Chain.lean` and raise `K`**. This is a decision, not
  an implementation detail, and slice 3k did not take it: no constant was moved.
* **The `6/2^128` one-time term is not needed on the new route.**
  `programIndices_steerPrograms`'s freshness side condition (`π ℓ ∉ {f, s}`) exists only to
  make `programmed_programmed` compose. `uniform_programmed_retarget`
  (`Proof/Retarget.lean`) replaces it with an unconditional reparametrisation, so the
  `6/2^128` in `chainOneTime` becomes slack rather than a charge. `Proof/Chain.lean` was
  **not** modified: the constant is still budgeted and now has margin.
* **New tools built this slice, all machine-checked and reusable.**
  `Proof/Retarget.lean`: `programmed_apply_label`, `programmed_programmed_label`,
  `shiftErased`/`shiftErasedEquiv`, `retarget`/`retargetEquiv`, `uniform_programmed_shift`,
  **`uniform_programmed_erased`** (a uniform permutation read through one programming is
  that programming together with an *independent uniform* erased image) and
  **`uniform_programmed_retarget`** (the intermediate programming may be dropped in law).
  Neither needs the ranges to be uniform. `Proof/Deferred.lean`:
  `twoStageGame_congr_support`, the transfer law with **two** second stages that need agree
  only on the support — this is what lets the off-curve results (no steering) and the
  on-curve results (steering = shift of the hidden part) be handled by different arguments
  in one application. `Proof/VisibleGame.lean`: `tableOfVisible` and
  `tableOfVisible_visibleCoordinates` (the released table is a function of the visible
  coordinates), `releasedPair`, `map_releasedPair_offCurve` and `map_releasedPair_onCurve`
  (the two joint laws step 7 has to match, both discharged from P4),
  `referenceRound_eq_twoStageGame` and `steeredReferenceRound_eq_twoStageGame` (the glue
  slice 3j asked for — both are `rfl`), `steeringTarget_offCurve`,
  `simulatedStageTwo_of_noTarget` and `steeredReleasedStageTwo_offCurve` (off the curve the
  simulator has no target, so the two second stages are the same function).
* **No constant moved, and no statement was weakened.** `Proof/Chain.lean` and
  `Proof/Privacy.lean` are byte-identical to slice 3j.

**Corrections from slice 3l — READ THIS WITH THE SLICE-3K BLOCK.**

* **`K` is now `16`, as `chainPerQuery` in `Proof/Chain.lean`, and the derivation is in
  that declaration's doc-comment.** Eight hops on the two machine-checked sides supply
  `8 q / 2 ^ 128` (`4 q / 2 ^ 128` each from `advantage_hybridGame_referenceGame_le` and
  `advantage_simulatedGame_steeredReferenceGame_le`); the steering hop is charged
  `8 q / 2 ^ 128` (four bad points, two per query direction, at `2 / 2 ^ 128` each). The
  `2 / 2 ^ 128` per point covers both `1 / (2 ^ 128 - q)` for `q < 2 ^ 127` and the
  hash-fiber chunk; for `q ≥ 2 ^ 127` the whole bound exceeds one and is free. `16` has
  slack over the honest figure (about `12.2`) on purpose: `workPerAdvantage_of_le` proves
  the tail for any `perQuery ≤ 2 ^ 28`, so the margin to the wall is still `2 ^ 24` and
  nothing in the chain depends on the value. `chainOneTime`, `chainOneTime_lt` and
  `chainOneTime_le` were **not** touched: the one-time terms do not depend on `K`, and the
  `6 / 2 ^ 128` freshness term is kept even though `uniform_programmed_retarget` makes it
  slack on the `retarget` route.
* **The obligation statement is byte-unchanged.** `Proof/Privacy.lean` was not modified at
  all this slice; `realGame_eq_hybridGame`, `hybridGame_close_to_idealGame` and
  `adaptivePrivacy` are byte-identical to `ab07aa8`, and the single `sorry` is still the
  original one at `hybridGame_close_to_idealGame`.
* **The assembly is done, and it is now the *only* thing that was left besides step 7.**
  `Proof/Assembly.lean` proves `workPerAdvantage_of_steering`: from the single hypothesis

  ```lean
  advantage (referenceGame (hybridBridge scalar) adversary parameter auxiliary)
    ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
      steeredReferenceGame (fun _ => bridgeKey.value) scalar adversary parameter auxiliary)
    ≤ steeringStep adversary parameter
  ```

  (`steeringStep = 8 q / 2 ^ 128 + 6 / 2 ^ 128`) it derives exactly the goal of
  `hybridGame_close_to_idealGame`, `sorryAx`-free. `chain_shares_eq` proves that the three
  shares sum to `chainPerQuery * q / 2 ^ 128 + chainOneTime` **as an equality**, so the
  accounting is machine-checked end to end and `chainPerQuery = 16` is validated. The hop
  was deliberately left as a *hypothesis* rather than a second `sorry`: the tree still has
  exactly one `sorry`, in its original place, and the residual obligation is one crisp
  inequality between two named games rather than a bare goal.
* **Slice 3k's fixed-target chunk-mass figure (`≈ 1.11 / 2 ^ 128`) is NOT provable by the
  counting argument it cites, and the chain does not need it.** A fiber is the arithmetic
  progression `target + k p` inside `2 ^ 384`. For the *low* chunk the members with a
  prescribed chunk value form a residue class of `k` modulo `2 ^ 128` and for the *high*
  chunk they form an interval in `k`, so both are countable by hand; but for the **middle**
  chunk the condition is `(target + k p) mod 2 ^ 256 ∈ I` with `|I| = 2 ^ 128`, and bounding
  the number of hits is an equidistribution statement about `p` modulo `2 ^ 256` (a
  three-distance / continued-fraction argument, with denominators up to `2 ^ 128`). The
  count is about `5.4` on average but nothing short of that analysis bounds the maximum.
  **The chain never needs a fixed target.** The steering gate's fiber target is that gate's
  own selected output `o x7 0`, which is the hidden part of the two-stage game: conditionally
  on the released table it is uniform (off the curve because the visible law is uniform, on
  the curve because `offsetTerm` has coefficient exactly one in it). So the law to bound is
  the **marginal** one -- a uniform field element and then a uniform sample of its fiber --
  and `hashFiber_total_difference` already puts that within `p / 2 ^ 384` of the uniform
  384-bit law. `Proof/Chunk.lean` finishes it: a digest is its three chunks
  (`digestChunkEquiv`), so a uniform digest has an exactly uniform chunk
  (`map_uniformDigest_chunk`), and hence **`fiberChunk_mass_le`**: every point mass of a
  128-bit chunk of a marginal hash-fiber sample is at most `1 / 2 ^ 128 + p / 2 ^ 384 ≤
  2 / 2 ^ 128`. That is the `2 / 2 ^ 128` the `chainPerQuery` derivation charges.
* **Three of the four bad points are cheap; the fourth (`y = π ℓ`) is the whole of the
  remaining work, and it needs lazy sampling.** With `ℓ` the selected label, `c_f` and `c_s`
  the two fiber chunks and `f = c_f ^^^ ℓ`, `s = c_s ^^^ ℓ`:
  * `π x = f` and `y = f` are conditions `c_f = π x ^^^ ℓ` and `c_f = y ^^^ ℓ`: one point
    each in `c_f`. Game `R(c/s)` -- the reference side of the hop -- **never mentions `f`**,
    so charging the bad mass on that side (which `advantage_bind_le_jointBad` permits) makes
    `c_f` a value the run does not read, and `hidden_label_bound` plus `fiberChunk_mass_le`
    bound them at `2 / 2 ^ 128` per log entry.
  * `π x = s` is one point in `c_s`, but **both** games program their stage-2 view with `s`,
    so neither side gets it for free; it still has to be charged against the conditional law.
  * `y = π ℓ` (the erased image) involves neither chunk. For **stage-1** log entries it is
    one point in `ℓ` (`ℓ = π⁻¹ y`) and `firstStage_hidden_le` already bounds it, because
    stage 1 never reads the key. For **stage-2** entries the adversary has been handed `ℓ`,
    and the honest bound is that `π ℓ` is uniform over the at least `2 ^ 128 - q` values the
    transcript has not pinned. That is a lazy-sampling statement and the tree has no route
    to it.
* **Every eager reparametrisation of `π` is circular, and this is now checked for
  `uniform_programmed_erased` too.** Slice 3k ruled out `retarget`/`swapRanges`. The same
  obstruction kills the `uniform_programmed_erased` route, which otherwise looks decisive:
  writing `ρ = π ℓ` and `π = programmed (programmed π ℓ f) ℓ ρ` turns the steered game into
  "stage 1 on `programmed π' ℓ ρ`, stage 2 on `programmed π' ℓ s`" with `ρ` a **free uniform
  block**, and the reference game into "stage 1 on `programmed (programmed π' ℓ s) ℓ ρ`,
  stage 2 on `programmed π' ℓ s`" -- two games differing **in stage 1 only**, which is
  exactly what §4 promised and what `firstStage_hidden_le` is built for. It cannot be used:
  `uniform_programmed_erased` takes its `label` and `range` as parameters *outside* the
  continuation, and `ℓ`, `f` and `s` are functions of the adaptively chosen input and of the
  stage-2 fiber samples. The bijection would have to be chosen before the first stage runs.
  **Do not re-attempt this either.** Conditioning on the transcript first is the only escape,
  and that is the lazy-sampling theorem.
* **What the lazy-sampling theorem has to say.** The eager model runs
  `program.run idealOracle` on a state holding a concrete `PermutationOracle FixedKeyIndex
  Block`. The lazy model carries a partial injective assignment per index and answers a
  fresh query by a uniform choice from the unused values. The theorem is that the two laws
  of `(result, log)` agree; its induction step is exactly
  `Cryptography.Permutation.programCompatiblePermutation_uniform` together with
  `compatiblePermutation_mass` / `injectiveAssignment_mass`. With it, `π ℓ` conditioned on a
  transcript of `q` entries is uniform over at least `2 ^ 128 - q` values, which is the
  missing `1 / (2 ^ 128 - q)`. Nothing under `Proof/` does this today, and it is the whole
  of the remaining work -- slice 3l did **not** build it, and its size was underestimated:
  it is a self-contained development (a lazy oracle, its state invariant, the run-level
  induction, and the bridge back to `idealOracle`), not a corollary of the counting core.

**Corrections from slice 3m -- the lazy-sampling theorem is LANDED.**

* **VCV-io does NOT supply a transferable eager/lazy framework for a permutation oracle, and
  the challenge's design note overstates what it gives.** `formal/Cryptography/RandomOracle.lean`
  imports `VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable`, whose two theorems are
  `evalSPMF_simulateQ_randomOracle_run'_eq_tableExtending` and its empty-cache corollary. They
  are about a random **function** oracle `D →ₒ R`: the eager object is a full table `g : D → R`,
  the lazy object is a `QueryCache`, and the two are glued by `tableExtending c g = fun t =>
  (c t).getD (g t)` -- overlay the cache on the table. **No analogue of `tableExtending` exists
  for a permutation**: a partial injective assignment cannot be overlaid on a permutation and
  still give a permutation, so the induction vehicle does not transfer. The workhorse
  `evalSPMF_uniformSample_bind_update` ("absorb a fresh uniform draw into the pre-sampled
  table") is exactly what has to be replaced, and its permutation analogue is the challenge
  library's own `programCompatiblePermutationEquiv`. Three further mismatches: VCV-io works on
  `OracleComp` with `SampleableType`, not the challenge's `OracleProgram`/`OracleHandler`; the
  entry's spec is `publicOracleSpec` with five query kinds and a `State`, not `D →ₒ R`; and
  `OracleHandler` is **deterministic** (`∀ query, State → Answer × State`), so a lazy handler
  cannot be written as an `OracleHandler` at all. What did transfer is the *shape*: generalise
  the cache (here, the assignment) and induct over the program, with a one-step marginalisation
  lemma as the induction step. That shape is what `Proof/Lazy.lean` follows.
* **The counting core that IS consumed is `programCompatiblePermutationEquiv`, not
  `programCompatiblePermutation_uniform`.** The marginal statement
  (`programCompatiblePermutation_uniform`: programming a fresh point of a uniform compatible
  permutation is uniform on the extended subtype) is **not strong enough**: after the
  `PMF.bind_comm` it only says the average over the erased image is right, and the induction
  needs the *joint* independence of the erased image and the programmed permutation. The
  library's `programCompatiblePermutationEquiv` is exactly that joint statement
  (`S ≃ T_{y} × ↑tᶜ`, `π ↦ (program π to y, π x)`), and it is what `compatibleSplit` wraps.
  `compatiblePermutation_count` / `compatiblePermutation_mass` / `injectiveAssignment_mass` are
  **not needed at all**: the fibre-cardinality argument they would serve is replaced by the
  explicit `repin` bijection `T_{y} ≃ T_{z}`, which is `π ↦ π.trans (swap y z)`.
* **`Proof/Lazy.lean` (new, ~1280 lines, `sorryAx`-free).** The development, in order:
  * `Assignment := Block → Option Block`, `AssignmentInjective`, `Compatible assign π`,
    `pinnedDomain` / `pinnedRange`, `pinnedEquiv` (the partial injection as an `Equiv` of its
    domain with its range), `compatible_iff` (the bridge to the library's `∀ a : s, π a = e a`
    shape), `nonempty_compatible` (an injective assignment is realised, via
    `Equiv.extendSubtype`), `unused_nonempty` / `unpinned_nonempty` (cardinality).
  * **Three total laws**, so no `Nonempty` instance ever has to be carried in a statement:
    `compatibleLaw assign : PMF (Equiv Block Block)` (uniform over the compatible permutations,
    `PMF.pure (Equiv.refl _)` on the unreachable non-injective branch), `freshValueLaw assign`
    (uniform over `{v | v ∉ pinnedRange assign}`) and `freshInputLaw assign` (uniform over
    `{i | assign i = none}`). This totality is what keeps the run-level statement readable:
    the conditional law of the permutation given the final transcript is just
    `compatibleLaw output.2`.
  * **`compatibleLaw_forward`** -- reading a uniform compatible permutation at an unpinned
    input is the same as drawing the answer from `freshValueLaw` first and conditioning the
    permutation on it. This is the marginalisation; it is `compatibleSplit` +
    `uniformOfFintype_bind_prod` + `PMF.bind_comm` + `repin`.
  * **`compatibleLaw_inverse`** -- the same for `π.symm` at an unpinned value, obtained by
    transporting `compatibleLaw_forward` along the **transposed assignment** `pinnedInput`
    (`pinnedInput assign v = some i ↔ assign i = some v`, `compatible_pinnedInput_iff`,
    `compatibleSymm`, `pinnedInput_update`). Doing the inverse direction from scratch would
    have doubled the file.
  * **`lazyAnswer` / `lazyRun`** -- the lazy handler and the lazy run. `lazyRun` is a direct
    `PMF`-valued recursion over `OracleProgram`, **not** an `OracleHandler`, because the
    challenge's handlers are deterministic. It answers a tracked `fixedForward` / `fixedInverse`
    from the assignment (pinned: return the pin; fresh: draw from `freshValueLaw` /
    `freshInputLaw` and extend), and every other query from the view. The invariant it
    maintains is `AssignmentInjective`, preserved by `update_injective` because the new value is
    drawn from the *unused* values.
  * **`lazy_query_step`** -- one query step, abstract in the eager and lazy continuations, with
    the induction hypothesis as a parameter. Nine branches; this is where the whole case
    analysis lives.
  * **`compatibleLaw_run`** -- the eager-to-lazy equivalence:
    ```lean
    ((compatibleLaw assign).bind fun permutation =>
        (program.run idealOracle (setPermutation state index permutation)).map fun output =>
          ((output.1, output.2.log), permutation)) =
      (lazyRun index program state assign).bind fun output =>
        (compatibleLaw output.2).map fun permutation => (output.1, permutation)
    ```
    i.e. sampling the whole permutation before the run and sampling only the transcript during
    the run and the permutation afterwards give the same law of `(result, log, permutation)`.
    Note the output keeps the permutation, which is what makes this usable: it says exactly
    that **conditionally on `(result, log)` the permutation is uniform over the permutations
    compatible with the final transcript.**
  * **`compatibleLaw_map_apply` / `compatibleLaw_map_symm_apply`** -- the conditional-uniformity
    corollary: given a transcript, `π input` at an unpinned input is *exactly* `freshValueLaw`,
    and `π.symm value` at an unpinned value is exactly `freshInputLaw`.
  * **`pinnedCount`, `lazyRun_pinnedCount`** -- a lazy run of a `budget`-query program pins at
    most `budget` further points, so the transcript of the whole run pins at most `q` points.
  * **`compatibleLaw_apply_le` / `compatibleLaw_symm_apply_le` and the `toOuterMeasure`
    singleton forms `compatibleLaw_singleton_le` / `compatibleLaw_symm_singleton_le`** -- the
    charge: with `pinnedCount assign ≤ budget`, any single value is hit with probability at
    most `(2 ^ 128 - budget)⁻¹`. Nat subtraction makes the statement unconditional (for
    `budget ≥ 2 ^ 128` the bound is `⊤`), so no `q < 2 ^ 127` side condition is needed here;
    the `1 / (2 ^ 128 - q) ≤ 2 / 2 ^ 128` step of the `chainPerQuery` derivation is where that
    side condition lives, and it is unchanged.
* **The two remaining bad points are NOT yet charged.** `Proof/Lazy.lean` supplies the missing
  ingredient and nothing else: the hop's own accounting still has to (i) put the steered and
  reference rounds into the `setPermutation` / `idealOracle` shape `compatibleLaw_run` expects,
  (ii) instantiate the union bound over the log with `compatibleLaw_singleton_le` as the
  per-entry charge, and (iii) fit that to `advantage_bind_le_jointBad`. That is the remaining
  oracle half; `steeringStep`'s `8 q / 2 ^ 128` already budgets `2 / 2 ^ 128` per point per
  direction, and `1 / (2 ^ 128 - q) ≤ 2 / 2 ^ 128` for `q < 2 ^ 127`, so **no constant has to
  move.**
* **Lean gotchas this slice, all of them about the dependent answer type.**
  * `request.Answer` is `Block` only after `cases request`, and it stays *syntactically*
    `(PublicQuery.fixedForward i x).Answer`. `rw` keys on the head symbol **and the type
    arguments**, so `rw [PMF.pure_bind]`, `rw [PMF.support_map]` and `rw [bind_of_map]` all
    fail with "did not find an occurrence" against a goal that visibly contains the pattern.
    Use `calc` with `exact`-elaborated steps (defeq, not keyed matching), give the lemma its
    explicit arguments (`PMF.pure_bind (value, assign) fun pair => …`), or state a **generic**
    helper (`eq_of_mem_support_pure`, `exists_of_mem_support_map`) whose own proof does the
    `rw` at uniform types.
  * `h ▸ member` on such a hypothesis leaves metavariables; `rw [h] at member` works, because
    `h`'s left-hand side is the hypothesis's own spelling.
  * `simp only [lazyAnswer, if_pos rfl, …]` leaves `if True then _ else _` and a residual
    `a = a` that differs only in the invisible type argument. Plain `simp` followed by `rfl`
    closes both.
  * `Nonempty` is a `Prop`, so `haveI`/`letI` of a nonemptiness proof is free of
    instance-mismatch problems -- but a `Nonempty` *under a binder* must be supplied as a
    `haveI foo : ∀ value, Nonempty (… value) := …` **before** the statement that needs it,
    or the statement will not elaborate.
  * `Fintype.card {x // x ∈ s}` and `Fintype.card ↑s` are the same type but `omega` does not
    know it; bridge with `Fintype.card_congr (Equiv.refl _)`.
  * The subtype `Fintype`s here are `Fintype.ofFinite _` global instances; do not `open
    Classical`, or `Subtype.fintype` becomes applicable and the instances diverge.

**Corrections from slice 3n -- READ THIS WITH THE SLICE-3M BLOCK.**

* **One tracked index suffices; `compatibleLaw_run` does NOT have to be generalised to a
  family.** Slice 3m §5.6 flagged that a `false` steering gate is programmed at *three*
  different `FixedKeyIndex` values (its three hash slots; a `true` gate at two pad slots),
  while `compatibleLaw_run` lazifies a single index. The single-index shape is right: the
  three permutations are independent, a permutation query names exactly one index, and each
  application of `compatibleLaw_run` is a rewriting of the *same* game law, so the tool may
  be applied once per index with the other two eager.
* **But the union bound must be keyed to the entry, not to the index, and this is
  budget-critical.** Applying the existing `q * bound` union bound once per steering index
  and adding the three results costs three times the honest figure and **does not fit
  `steeringStep`**. The arithmetic: the honest per-log-entry cost is `4 / 2 ^ 128` (a log
  entry is either forward or inverse, so it has **two** bad points, each charged at most
  `2 / 2 ^ 128`), i.e. `4 q / 2 ^ 128` against the reserved `8 q / 2 ^ 128`; charging per
  index instead gives `3 * 4 q / 2 ^ 128 = 12 q / 2 ^ 128`, which exceeds the reserved
  share. The fix is `toOuterMeasure_exists_mem_keyed_le` (`Proof/Erased.lean`): the bad set
  of an entry at every index other than its own is **empty**, so summing the per-index
  bounds costs one charge per log entry. No constant has to move, and `Proof/Chain.lean`
  was not touched.
* **`compatibleLaw_run` alone applies to NEITHER game of the hop, and this is the real
  shape problem slice 3m could not see.** Its statement is about `program.run idealOracle
  (setPermutation state index permutation)` -- a run whose oracle at the tracked index *is*
  the sampled permutation. Both games of the hop run their **second stage on a programmed
  view**: the reference game on `programmed pi l s`, the steered one on `programmed
  (programmed pi l f) l s`. So the second stage is not of that shape, and the tool cannot
  be pointed at it directly.
* **The missing glue is an exact product, and it is cheap: `compatibleLaw_programmed`.**
  Conditionally on the first stage's transcript `assign` -- injective, with the selected
  label `l` unpinned and the steered range `s` unused, both of which are bad points the hop
  already charges --

  ```lean
  ((compatibleLaw assign).bind fun permutation =>
      continuation (programmed permutation label range) (permutation label)) =
    (freshValueLaw assign).bind fun erased =>
      (compatibleLaw (Function.update assign label (some range))).bind fun view =>
        continuation view erased
  ```

  the programmed view and the erased image `rho = pi l` are **independent**: the view is
  uniform over the permutations compatible with the transcript re-pinned at `l` to `s`, and
  `rho` is uniform over the values the transcript has not pinned. It is
  `compatibleLaw_forward` followed by the `repin` bijection of `Proof/Lazy.lean`, and it is
  an equality with no slack. Counting check: `(2 ^ 128 - k)! = (2 ^ 128 - k - 1)! * (2 ^ 128
  - k)`. So the second stage learns **nothing** about `rho`, and `erased_touch_le` charges
  each second-stage log entry `1 / (2 ^ 128 - q)` -- exactly what the accounting budgets.
  The tool is therefore applied **twice**, once per stage, with `compatibleLaw_programmed`
  as the bridge, rather than once over a two-stage run.
* **The bad-point census of the hop, per log entry, with the side each is charged on.**
  Write `l` for the selected label of the steering gate, `c_f` for the honest fiber chunk,
  `c_s` for the steered chunk, `f = c_f ^^^ l`, `s = c_s ^^^ l`, `rho = pi l`. Charging on
  the reference side `R(c/s)` (`advantage_bind_le_jointBad` permits it) and writing `B =
  programmed pi l s` for its stage-2 view:
  * stage-1 forward entry `x`: `pi x = f` (one point in `c_f`) and `pi x = s` (one point in
    `c_s`). Both chunks are sampled **after** the first stage, so both are deferrable and
    `fiberChunk_mass_le` charges them at `2 / 2 ^ 128`.
  * stage-1 inverse entry `y`: `y = f` (one point in `c_f`) and `y = rho`, which is
    `l = pi.symm y` -- one point in the **label**, and the first stage never reads the key,
    so `firstStage_hidden_le` charges it at `1 / 2 ^ 128`.
  * stage-2 forward entry `x`: `pi x = f` is `B x = c_f ^^^ l`, and `R(c/s)` never reads
    `c_f` at all (its fiber sample is at the *shifted* outputs, `setSteering`), so it is
    deferrable past the whole game; `pi x = s` is `B x = rho`.
  * stage-2 inverse entry `y`: `y = f` (again `c_f`), and `y = rho`.

  So exactly **two** points per entry, and the only ones the lazy theorem is needed for are
  the stage-2 `rho` points. Note the pleasant collapse: a stage-2 *forward* bad point is
  also a `rho` condition (`pi x = s` iff `B x = rho`), so both directions are covered by the
  single `point : outcome -> Query -> Block` parameter of `erased_touch_le`.
* **The route for step 7 is: charge FIRST, then transfer.** Slice 3m's plan had
  `twoStageGame_congr_support` doing the whole identification, with the double programming
  discharged inside its `stageAgree` hypothesis. That cannot work: `stageAgree` is an
  *equality* of second stages, and the two second stages differ exactly at the four points.
  The correct order is
  1. `S = steeredReferenceGame u` is within the bad mass of `S'`, the same two-stage game
     whose second stage samples **one** fiber family at the shifted outputs
     (`uniformHashFibers_setSteering` + `shiftSteering_eq_setSteering` + `steerTo_eq_map`
     turn the steering's two samples into one) and programs **once**
     (`programAll_steerRequests` + `publicAnswer_steeringHidden`). This hop is
     `advantage_bind_le_jointBad` with the census above.
  2. `S' = referenceGame (c/s)` **exactly**, by `twoStageGame_congr_support` applied to
     `steeredReferenceRound_eq_twoStageGame` and `referenceRound_eq_twoStageGame` with
     `rest' = shiftSteering delta` of the selected outputs, the joint law discharged by
     `map_releasedPair_offCurve` / `map_releasedPair_onCurve`, and the second stages now
     literally equal (off the curve by `steeredReleasedStageTwo_offCurve`).

  In this order the `swapRanges` reparametrisation of `programIndices_steerPrograms` is
  never needed -- which is the point, since every eager reparametrisation is circular
  (slices 3k, 3l).
* **`Proof/Erased.lean` (new, ~370 lines, `sorryAx`-free).** `compatibleLaw_programmed`,
  `erased_run_independent` (the joint law of the stage-2 run and the erased image factors),
  `freshValueLaw_singleton_le`, `erased_touch_le` (the per-entry charge, with the log-length
  bound folded in), `toOuterMeasure_exists_mem_keyed_le` (the entry-keyed union bound),
  `programmed_apply` / `programmed_symm_apply`,
  `programmed_programmed_apply_of_ne` / `programmed_programmed_symm_apply_of_ne` (the
  pointwise algebra of the four points), `steeringHidden` and `publicAnswer_steeringHidden`
  (the identical-until-bad input, in the `publicAnswer` form `run_idealOracle_agree`
  consumes), and the bridge from the games to the tool: `emptyAssignment_injective`,
  `pinnedCount_empty`, `compatibleLaw_empty`, `setOracleAt`, `setPermutation_eq`,
  `swapOracleAt`, `uniform_bind_setOracleAt` (one index of a uniform permutation family may
  be resampled after everything else, the analogue of `uniform_bind_setOracle`).
* **What step 7 still owes after slice 3n.** The plumbing, not the mathematics: put both
  rounds into the two-stage shape under one sample, rewrite the steering into one fiber
  sample plus one unconditional programming, instantiate `advantage_bind_le_jointBad` with
  the census above (three deferrals -- the two chunks past the stages that do not read them,
  and the label -- plus `erased_touch_le` at each of the two or three steering indices,
  recombined by `toOuterMeasure_exists_mem_keyed_le`), and then apply
  `twoStageGame_congr_support`. No constant moves.
* **Lean gotchas this slice.**
  * `rw [someDef]` fails with "Failed to rewrite using equation theorems" when the
    definition's body is a **structure literal** (`setOracleAt oracle index p :=
    <fun other => ...>`). Use `show` with the projected body instead; the defeq check is
    cheap.
  * `cases h : scrutinee with` **substitutes the scrutinee into the goal**, so a later
    `rw`/`Finset.sum_congr` keyed on the original spelling ("`key entry`") fails with "did
    not find an occurrence" against a goal that now says `none` or `some target`. Write the
    branches against the substituted form.
  * `Finset.sum_congr rfl proof` cannot infer the right-hand summand from `proof`'s type
    (higher-order unification on `g index = 0`). State the summation equality as a typed
    `have` with both sides written out, then `rw` it.
  * `zero_le` in this context takes **no** explicit argument; `zero_le charge` and
    `zero_le _` both fail with "function expected".
  * `publicAnswer_view_congr` lives in `Proof/HybridChain.lean`. A leaf file under
    `Proof/` should inline the five-case `cases query` analysis rather than import the whole
    `H`-side chain for it.
  * A file that mentions `BaseField` needs `open BN254`; without it the error surfaces as
    "stuck at solving universe constraint" on an unrelated earlier line.

**What P10 still has to do (as of slice 3n).** Exactly one thing: the hypothesis of
`workPerAdvantage_of_steering` (`Proof/Assembly.lean`). Everything else in the chain,
including the final assembly and the arithmetic, is machine-checked. The hop splits into

(a) the **visible-law half**, ready since slice 3k: apply `twoStageGame_congr_support` to
`referenceRound_eq_twoStageGame` and `steeredReferenceRound_eq_twoStageGame`, discharging
the joint law by `map_releasedPair_offCurve` off the curve and `map_releasedPair_onCurve`
on it (hidden part on the steered side `shiftSteering δ` of the selected outputs), and the
second stages by `steeredReleasedStageTwo_offCurve` off the curve and by
`steer_programSelected` + `uniformHashFibers_setSteering` + `steerTo_eq_map` +
`programAll_steerRequests` on it; and

(b) the **oracle half**, which reduces the double programming of the steering gate to the
reference game's single programming. Its bad points are priced by `fiberChunk_mass_le`
(`Proof/Chunk.lean`), `firstStage_hidden_le` (`Proof/Hidden.lean`) and `erased_touch_le`
(`Proof/Erased.lean`, slice 3n), recombined by `toOuterMeasure_exists_mem_keyed_le`. **All
the tools exist now; what is left is the bookkeeping -- see the census and the two-step
route in "Corrections from slice 3n".** Note that (a) must run *after* (b), not around it:
`twoStageGame_congr_support` needs the two second stages to be equal, which they are only
after the bad event has been charged. Every eager reparametrisation has been checked and
ruled out (slices 3k and 3l); do not re-attempt them.

**The historical plan below is kept for context.** The whole `H` side is done: steps 1 and 3 (slice 3h,
`Proof/HybridChain.lean`) and step 2 plus the identification with `R(c/s)` (slice 3i,
`Proof/HybridReference.lean`). The whole `S` side up to the steering is done: steps 4, 5 and
6 (slice 3j, `Proof/SimulatedChain.lean`) and the `S` side's own step 2 plus the
identification with `R(u)` + steering (slice 3j, `Proof/SimulatedReference.lean`). What is
left, in order:

(i) **step 7, in two halves (slice 3k)**. The *visible-law* half is ready: apply
`twoStageGame_congr_support` to `referenceRound_eq_twoStageGame` and
`steeredReferenceRound_eq_twoStageGame`, discharging the joint law by
`map_releasedPair_offCurve` off the curve and `map_releasedPair_onCurve` on it (with the
hidden part on the steered side taken to be `shiftSteering δ` of the selected outputs), and
the second stages by `steeredReleasedStageTwo_offCurve` off the curve and by
`steer_programSelected` + `uniformHashFibers_setSteering` + `steerTo_eq_map` +
`programAll_steerRequests` on it.

The *oracle* half is the open one: the double programming of the steering gate has to be
reduced to the reference game's single programming, and that step is **not** bounded by any
label deferral. See "Corrections from slice 3k" for why, for the four bad points, and for
the random-permutation tool (`Cryptography/Permutation.lean`) the bound has to be built on.
It also needs a driver decision on `K` in `Proof/Chain.lean`.

Do **not** re-attempt the `swapRanges` route of `programIndices_steerPrograms`, and do not
try to move the hop between steps 4 and 5: both are analysed and ruled out above.

(ii) chain `advantage_hybridGame_referenceGame_le`, step 7 and
`advantage_simulatedGame_steeredReferenceGame_le` with `advantage_trans` (the `S` side
reaches the middle game `R(c/s)` from the other end, so one `advantageSymm` orientation step
is needed) and close with `workPerAdvantage_of_chain`.

**The constant assignment (slice 3h, updated slices 3i, 3j and 3l).** The budget is
`chainPerQuery·(q₁+q₂)/2^128 + chainOneTime` with `chainPerQuery = 16`,
`chainOneTime = sideOneTime + sideOneTime + 6/2^128`,
`sideOneTime = 2/p + 1270·(p/2^384)`. **No one-time constant moved in slice 3i, 3j or 3l;
slice 3l raised only the per-query constant, from `10` to `16`.**

| step | which side | per-query | one-time | status |
|---|---|---|---|---|
| 1 (reparametrise `π`) | H | 0 | 0 | **done** (`hybridGame_eq_fresh`) |
| 3, hop A (stage 1 → `π°`) | H | `2q₁/2^128 ≤ 2q/2^128` | 0 | **done** (`advantage_firstView_le`) |
| 3, hop B (stage 2 → selected labels) | H | `2q/2^128` | 0 | **done** (`advantage_secondView_le`) |
| 2 (mask `F*→F`) | H | 0 | `2/p` | **done** (`advantage_digestedGame_maskedGame_le`) |
| 2 (1270 digests → field + fiber) | H | 0 | `1270·p/2^384` | **done** (`advantage_maskedGame_fiberedDigestGame_le`) |
| 2 (fiber sample → selected outputs) | H | 0 | 0 | **done** (`fiberedDigestGame_eq_fiberGame`) |
| 2 (identify with `R(c/s)`) | H | 0 | 0 | **done** (`fiberGame_eq_referenceGame`) |
| 4 (reparametrise `π`) | S | 0 | 0 | **done** (`simulatedGame_eq_fresh`) |
| 5 (stage 1 → `π°`) | S | `2q₁/2^128 ≤ 2q/2^128` | 0 | **done** (`advantage_firstView_le`) |
| 6 (stage 2 unselected, steering blind to it) | S | `2q/2^128` | 0 | **done** (`advantage_secondStage_le`) |
| 2 twin (mask `F*→F`) | S | 0 | `2/p` | **done** (`advantage_steeredDigestedGame_steeredMaskedGame_le`) |
| 2 twin (1270 digests → field + fiber) | S | 0 | `1270·p/2^384` | **done** (`advantage_steeredMaskedGame_steeredFiberedDigestGame_le`) |
| 2 twin (fiber sample → selected outputs) | S | 0 | 0 | **done** (`steeredFiberedDigestGame_eq_steeredFiberGame`) |
| 2 twin (identify with `R(u)` + steering) | S | 0 | 0 | **done** (`steeredFiberGame_eq_steeredReferenceGame`) |
| 7 (steering removal and the visible-law identification) | S | `8q/2^128` (`steeringStep`) | `6/2^128` | open (slice 3k built the glue, the visible joint laws, the off-curve half and the reparametrisation tool; slice 3l priced the chunk points and proved the assembly around the hop; slice 3m built the lazy-sampling theorem; slice 3n built the erased-image independence, the four-point algebra and the entry-keyed union bound -- only the plumbing is left) |
| assembly (triangle + `workPerAdvantage_of_chain`) | — | 0 | 0 | **done** (`workPerAdvantage_of_steering`, `chain_shares_eq`) |

Slice 3h consumed `4·(q₁+q₂)/2^128` of the per-query budget and none of the one-time budget.
**Slice 3i consumed exactly one `sideOneTime`** of the one-time budget and none of the
per-query budget. Together the `H` side costs `4·(q₁+q₂)/2^128 + sideOneTime`
(`advantage_hybridGame_referenceGame_le`). **Slice 3j consumed `4·(q₁+q₂)/2^128` of the
per-query budget and the second `sideOneTime`, and nothing else**
(`advantage_simulatedGame_steeredReferenceGame_le`). What is left for step 7 is exactly
`steeringStep = 8·(q₁+q₂)/2^128 + 6/2^128`, and `chain_shares_eq` proves that the three
shares sum to exactly `16·(q₁+q₂)/2^128 + chainOneTime`. Slice 3l moved only
`chainPerQuery`; `chainOneTime` and `Proof/Privacy.lean` were not modified.

One thing the slice-3b analysis had that this chain does **not** need: hiding all 1270
unselected-label values by an explicit shift (absorbed by `P4`). Its `(2^128 − q)`
denominators, on the other hand, **are** needed — by step 7 and only by step 7. Every other
hop samples the hidden label fresh and hits with probability exactly `k/2^128`; step 7's
erased image `π ℓ` is a function of the permutation and has no such bound (slice 3k §3,
slice 3l).

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
| P10 | assemble §4 with `advantageTriangle` / `event_difference_le` and P8 | assembly layer `Proof/Chain.lean`: `advantage_bind_le_bad`, `advantage_bind_le_jointBad`, `advantage_bind_le_totalDifference`, `advantage_bind_le_of_le`, `advantage_trans`, `sideOneTime`, `chainOneTime`, `chainOneTime_lt`, `workPerAdvantage_of_chain`; first hop's algebra `Proof/Reparametrise.lean`: `usedLabel`, `programFamily_apply`, `freshDigest`/`freshPad`/`freshHash`, `curveGarble_programFamily`, `freshEquiv`, `uniform_map_freshEquiv`; `H`-side steps 1 and 3 `Proof/HybridChain.lean`: `setKey`/`uniform_bind_setKey`, `hybridTwoStage`, `hybridOn`, `hybridGame_eq_hybridOn`, `hybridGame_eq_split`, `freshValue`, `usedPrograms`, `programFamily_eq_programIndices`, `uniform_bind_usedPrograms`, `hybridFresh`, `hybridGame_eq_fresh`, `queryLabelIndex`, `usedHidden`, `UsedBad`, `usedLabel_eq_keyLabel`, `publicAnswer_usedPrograms`, `bind_pairLaw`, `advantage_firstView_le`, `publicAnswer_permutation_congr`, `programIndices_congr_at`, `digestedRaw`, `selectedPrograms_selected`/`_unselected`, `unreadQueryIndex`, `SelectedBad`, `publicAnswer_selectedPrograms`, `selectedStageTwo`/`_unread`/`_length`, `usedStageTwo`/`_agree`, `bind_stageLaw`, `secondBad`, `secondBad_mass_le`, `advantage_secondView_le`, `hybridData`, `digestedReference`, `advantage_hybridGame_digestedReference_le`; `H`-side step 2 and the `R` identification `Proof/HybridReference.lean`: `uniformOfFintype_bind_bijection`, `hybridData_eq_uniform`, `ReferenceDatum` with its projections, `referenceRaw`, `referenceCircuit`, `digestedBody`, `fiberedBody`, `referenceOf`, `hybridCircuit_eq_referenceCircuit`, `digestedGame`, `digestedSampleEquiv`, `digestedReference_eq`, `maskedGame`, `advantage_digestedGame_maskedGame_le`, `fiberedDigestGame`, `advantage_maskedGame_fiberedDigestGame_le`, `digestField_of_mem_uniformHashFibers`, `selectedPrograms_setGate`, `selectedStageTwo_setGate`, `uniformHashFibers_selected`, `fiberGame`, `fiberedDigestGame_eq_fiberGame`, `referenceRound`, `referenceGame_eq`, `referenceGame_eq_split`, `referenceSampleEquiv`, `fiberGame_eq_referenceGame`, `advantage_digestedReference_referenceGame_le`, `advantage_hybridGame_referenceGame_le`; `S`-side steps 4–6 `Proof/SimulatedChain.lean`: `hashBytes_congr`, `padBytes_congr`, `bitEvaluate_congr`, `evaluateDigit_congr`, `curveEvaluate_congr`, `fresh_congr`, `programIfFresh_congr_at`, `programAll_congr_at`, `programAll_untouched`, `publicAnswer_programAll_congr`, `simulateRequestLaw`/`_none`/`_some`/`_support`, `simulateEncode_eq_map`, `simulatedStageTwo_eq`, `steerRequestLaw_support`, `steerRequestLaw_congr`, `simulatedStageTwo_agree`, `usedSimulatedStageTwo`, `selectedSimulatedStageTwo`, `programSelected_stageTwoState`, `selectedSimulatedStageTwo_unread`, `simulatedStageTwo_length`, `programIndices_selected_congr`, `usedSimulatedStageTwo_agree`, `simulatedTwoStage`, `simulatedOn`, `simulatedGame_eq_simulatedOn`, `simulatedGame_eq_split`, `simulatedFresh`, `simulatedGame_eq_fresh`, `SimulatedDatum`, `simulatedData`, `simulatedCircuit`, `simulatedGame_eq_used`, `steeredDigested`, `advantage_simulatedGame_steeredDigested_le`; `S`-side step 2 and the `R(u)` identification `Proof/SimulatedReference.lean`: `steeredDigestedBody`, `steeredFiberedBody`, `simulatedData_eq_uniform`, `simulatedCircuit_eq_referenceCircuit`, `steeredDigestedGame`, `steeredSampleEquiv`, `steeredDigested_eq`, `steeredMaskedGame`, `advantage_steeredDigestedGame_steeredMaskedGame_le`, `steeredFiberedDigestGame`, `advantage_steeredMaskedGame_steeredFiberedDigestGame_le`, `steeredFiberGame`, `steeredFiberedDigestGame_eq_steeredFiberGame`, `steeredReferenceRound`, `steeredReferenceGame`, `steeredFiberGame_eq_steeredReferenceGame`, `advantage_steeredDigested_steeredReferenceGame_le`, `advantage_simulatedGame_steeredReferenceGame_le`; the step-7 glue `Proof/Retarget.lean` + `Proof/VisibleGame.lean` (slice 3k); the chunk mass `Proof/Chunk.lean` (slice 3l): `digestChunks`, `joinChunks`, `joinChunks_digestChunks`, `digestChunkEquiv`, `card_block`, `uniformOfFintype_map_fst`/`_snd`, `map_uniformDigest_chunk`, `uniformDigest_chunk_apply`, `fiberChunk_mass_le`; the assembly `Proof/Assembly.lean` (slice 3l): `steeringStep`, `chain_shares_eq`, `workPerAdvantage_of_steering`; **the lazy-sampling theorem `Proof/Lazy.lean` (slice 3m)**: `Assignment`, `AssignmentInjective`, `Compatible`, `pinnedDomain`/`pinnedRange`/`pinnedEquiv`, `compatible_iff`, `nonempty_compatible`, `unused_nonempty`/`unpinned_nonempty`, `compatible_update_iff`, `update_injective`, `compatibleLaw`/`freshValueLaw`/`freshInputLaw`, `uniformOfFintype_bind_of_equiv`, `bind_of_map`, `repin`, `compatibleSplit` (+ `_fst`/`_snd`), `compatibleLaw_forward`, `pinnedInput` (+ `_eq_some_iff`/`_eq_none`/`_injective`/`_update`), `compatible_pinnedInput_iff`, `compatibleSymm`, `compatibleLaw_bind_symm`, `compatibleLaw_inverse`, `setPermutation` (+ the four `publicAnswer_setPermutation_*`), `lazyAnswer`, `lazyRun`, `lazy_query_step`, **`compatibleLaw_run`**, `pinnedCount`, `pinnedDomain_update`, `pinnedCount_update_le`, `card_unused`, **`compatibleLaw_map_apply`**/**`_map_symm_apply`**, `uniform_map_val_apply_le`, **`compatibleLaw_apply_le`**/**`_symm_apply_le`**, `lazyAnswer_pinnedCount`, **`lazyRun_pinnedCount`**, `compatibleLaw_singleton_le`/`_symm_singleton_le`; **the erased-image independence `Proof/Erased.lean` (slice 3n)**: `compatibleLaw_programmed`, `erased_run_independent`, `freshValueLaw_singleton_le`, **`erased_touch_le`**, **`toOuterMeasure_exists_mem_keyed_le`**, `programmed_apply`/`programmed_symm_apply`, `programmed_programmed_apply_of_ne`/`_symm_apply_of_ne`, `steeringHidden`, `publicAnswer_steeringHidden`, `emptyAssignment_injective`, `pinnedCount_empty`, `compatibleLaw_empty`, `setOracleAt`, `setPermutation_eq`, `setOracleAt_permutation`, `setOracleAt_self`, `swapOracleAt`, `uniform_bind_setOracleAt` | **open** (both sides, the accounting and the assembly are done; only the steering hop is not) |

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

* **`split` on a `match` does not generalise the scrutinee for the other side of the
  goal.** When both sides of an equality match on the same expression, `split` splits only
  one of them and leaves the other's `match` intact. Give the definition an `Option.elim`
  body plus two equation lemmas (`_none`, `_some`) and rewrite with them, or use
  `cases h : scrutinee` followed by `simp only [theDefinition, h]`.
* **`PMF.apply_eq_zero_iff` takes the law and the point explicitly** (`(PMF.apply_eq_zero_iff
  _ _).mpr member`). It is the way to drop the off-support terms of a `tsum` after
  `PMF.bind_apply` when two continuations agree only on the support.
* **`congrArg (fun value => _ * value) proof` is a trap.** The underscore becomes a
  metavariable that the elaborator solves from the *other* side of the equation and the two
  factors get unified. Name the equation with `have` and `rw` it instead.
* **A `rw [h]` with `h : circuit.1 = …` rewrites every occurrence**, including the ones a
  later `exact` needs to keep in the original spelling. Wrap the rewrite in
  `show f circuit.1 = f … from congrArg f h` to hit exactly one subterm.
* **`(programAll state requests).log = state.log` closes with `programAll_log`, but the
  residual `(stageTwoState …).log = (stageTwoState …).log` does not close by `rfl` cheaply**
  — add the one-sided `stageTwoState_log` rewrites, as for the other projections.
* **`push_neg` is deprecated**; write the negation out by hand
  (`intro request member equal; exact touched ⟨request, member, equal⟩`).
* **Unfolding a `FixedKeyOracle` field on one side only leaves the two sides out of sync.**
  In `bitEvaluate_congr` a `show` of the unfolded `hashToField` form on the left does not
  line up with the untouched right; `simp only [fixedKeyGate, BitAdaptor.fixedKeyOracle]`
  first, then `rw` the digest congruence.

* `congr 1`, `rfl`, and `simp` on terms containing `BaseField` arithmetic can hit
  `maximum recursion depth` (ZMod numerals). Use `Coordinates.ext ?_ ?_ …` with
  `dsimp only [...]` per field, `change` to the explicit form, then `rw`/`ring`
  (see `releaseEquiv`, `offsetTerm_releaseMiddle`).
* `Fintype (BitVec 256)` is declared in `Proof/Reference.lean`; `Fintype (BitVec 384)` in
  `Proof/Simulator.lean`; `Fintype Coordinates` via `Coordinates.data`.
* The `sorry` must remain the one at `hybridGame_close_to_idealGame` until the steering hop
  is proved. Do not move it into a helper lemma: `workPerAdvantage_of_steering` already
  isolates the residual obligation as a *hypothesis*, which gives the same clarity without a
  second place for a `sorry` to hide.
* **`extractLsb'_append_extractLsb'_eq_extractLsb'` is the cheap way to rebuild a `BitVec`
  from adjacent slices**; right-associate the appends so the merges fire from the low end
  (`joinChunks`). A `Fintype.card` equality between a `BitVec` and a product of `BitVec`s
  needs `← pow_add`, not `ring` (`ring` compares 116-digit numerals).
* **`Equiv.ofBijective` + `Fintype.bijective_iff_injective_and_card` avoids proving
  `right_inv`** when one direction is a clean rewrite and the cardinalities match
  (`digestChunkEquiv`).
* `PMF.map f law` is definitionally `law.bind fun value => PMF.pure (f value)`, so
  `bind_apply_sub_le` applies to two mapped laws with a `fun _ => rfl` bridge
  (`fiberChunk_mass_le`).
* **A structure declared under `Construction/` has no `ext` lemma** (only `@[ext]`
  structures do). Declare the field-wise equality in `Proof/` instead and prove it by
  `obtain ⟨_, …⟩ := first; obtain ⟨_, …⟩ := second; simp_all` (`curveTable_ext`).
* An `Equiv` whose `toFun` is a lambda needs a `show` before `rw`: `left_inv` presents the
  goal as `(fun other => value ^^^ other) ((fun other => value ^^^ other) other) = other`
  and `rw` will not beta-reduce it (`xorBlock`).
* `Vector.ext fun position member => ?_` leaves a `getElem` goal; combine
  `Vector.getElem_ofFn` with `← Vector.get_eq_getElem (index := ⟨position, member⟩)` to get
  back to the `.get` form the coordinate lemmas are stated in
  (`tableOfVisible_visibleCoordinates`).
* Both `twoStageGame` glue lemmas are `rfl`: a round whose only uses of the sampled
  coordinates are the released table and the selected outputs is *literally* a
  `twoStageGame` once those two are named. Name them before trying to prove anything.
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
