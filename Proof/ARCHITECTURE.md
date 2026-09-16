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
  exchange. That is the open half of P6.

Two things the slice-3b analysis had that this chain does **not** need: hiding all 1270
unselected-label values by an explicit shift (absorbed by `P4`), and the `(2^128 − q)`
denominators (the `R`-side bounds sample the hidden label fresh, so each log entry hits with
probability exactly `k/2^128`).

## 5. Lemma list, dependencies, status

| id | content | file / name | status |
|---|---|---|---|
| P1 | programming involution `(π, r) ↦ (π programmed at ℓ to r, π ℓ)`; uniform `π` = uniform `π°` programmed at fresh uniform `r`; family version over `FixedKeyIndex` | `Proof/Programming.lean`: `programAt`, `programAtEquiv`, `uniform_programAt`, `programFamily`, `uniform_programFamily` | **done** |
| P2 | deterministic identical-until-bad for logged runs: same log, views agreeing off `bad` ⇒ same `(result, log)` law on good logs; bind form of `identical_until_bad`; log monotone, log length ≤ initial + budget | `Proof/Logged.lean`: `run_idealOracle_agree`, `bind_identical_until_bad`, `run_idealOracle_log_mono`, `run_idealOracle_log_length` | **done** |
| P3 | independence bad-bounds: union bound over a log (`hidden_label_bound`); one label of a uniform key is a uniform block (`setKeyLabel` involution, `map_keyLabel_uniform`, `uniform_keyLabel_mem`); hidden sets of one programmed permutation, 2 per direction (`forwardHidden`, `inverseHidden`, `hiddenLabels_card`, `publicAnswer_programIndices_single`); stage-1 bound with the key sampled up front (`firstStage_key_deferred`, `firstStage_hidden_le`) | `Proof/Hidden.lean` | **stage 1 done**; stage-2 (unselected-label) bound open |
| P4 | static bijection raw ↔ middle; `c0` affine in `mask`; visible law uniform off-curve, shift law on-curve | `Proof/Reference.lean`: `middleEquiv`, `Coordinates.table_c0_eq`, `visibleCoordinates_offCurve`, `visibleCoordinates_onCurve` | **done** |
| P5 | deferred sampling: transfer form `twoStageGame_congr` (equal joint laws of `(view, rest r)` per first-stage result ⇒ equal games) and factored form `twoStageGame_eq_deferredGame`; both by `tsum_map_mul` + `ENNReal.tsum_comm` | `Proof/Deferred.lean`: `twoStageGame`, `deferredGame`, `twoStageGame_apply`, `twoStageGame_congr`, `twoStageGame_eq_deferredGame`, `map_view_of_joint` | **done** |
| P6 | TV facts: total difference `∑ |law₁ − law₂|` with triangle inequality and both bind sub-additivities (`bind_apply_sub_le` swaps the sampled law, `bind_apply_sub_le_of_le` swaps the continuation); `U(F*)` vs `U(F)` total difference `2/p`; one 384-bit digest vs (`U(F)` then `uniformHashFiber`) total difference `≤ p/2^384` (fiber sizes are within one residue block of `2^384/p`, by the two injections `fiberElement`/`fiberIndex`) | `Proof/Distance.lean`: `totalDifference`, `totalDifference_triangle`, `bind_apply_sub_le`, `bind_apply_sub_le_of_le`, `mask_total_difference`, `card_hashFiber_lower`/`_upper`, `count_mul_difference_le`, `hashFiber_total_difference` | **per coordinate done**; the 1270-gate product (tensorisation) open |
| P7 | `steer` in deferred form: the programmed reference view releases every selected output and hence `bridgeKey + mask·curveGap`, so on-curve `current = u` and `wanted = o x7 0 + (c/s − u)` — the steering is `shiftMiddle (c/s − u)` on the visible data; the double programming (honest, then steered) of the steering gate is `R`'s single programming of the shifted outputs on `π° ↦ swap(honest range, steered range) ∘ π°` | `Proof/DeferredSteering.lean`: `swap_trans_swap`, `programmed_programmed`, `programIndices_programIndices`, `hashToField_programSelected`, `decrypt_programSelected`, `evaluate_programSelected`, `curveEvaluate_programSelected`, `steerTo`, `steer_programSelected`, `steerPrograms`, `programIndices_steerPrograms` | **core done**; the `programAll` → `programIndices` bridge and the fiber marginal open |
| P8 | arithmetic tail `ε ≤ K q/2^128 + ε₀`, `K ≤ 2^28`, `ε₀ ≤ 2^-101` ⇒ `WorkPerAdvantage 100 (q+1) ε`; `advantage ≤ 1` | `Proof/Reference.lean`: `workPerAdvantage_of_le`, `advantage_le_one` | **done** |
| P9a | `R(b)` as a `PMF Bool`: `programIndices` (unconditional partial programming), `gateKey`/`selectedLabel`/`slotRange`/`tableRow`, `selectedPrograms`, `HashFibers`/`uniformHashFibers`, `programSelected`, `referenceStage2`, `referenceGame`; `run_idealOracle_support` (a run changes only the log); `selectedPrograms_hash`/`_pad`/`_label` | `Proof/ReferenceGame.lean` | **done** |
| P9b | unfold `idealGame` for `hybridSimulator` and `simulator` into the shape of §4 (as `hybridGame_eq_core` does), marginalize unused tape fields (`uniform_bind_setBridge` pattern) | `Proof/Privacy.lean` has the hybrid half | open |
| P10 | assemble §4 with `advantageTriangle` / `event_difference_le` and P8 | — | open |

Dependencies: P9a needs P4's definitions; P3 needs P2 (log length) and P9a; P5 needs P4; P7 needs
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
