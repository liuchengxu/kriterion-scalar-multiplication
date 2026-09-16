# Proof architecture for `hybridGame_close_to_idealGame`

Status of the tree: every obligation is proved except the single `sorry` at
`Proof/Privacy.lean`, theorem `hybridGame_close_to_idealGame` (statement must stay
byte-identical). This document is the plan for closing it, the pieces that are already
machine-checked, and the constant it produces. The next slice must inherit it rather than
re-derive it.

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

`R(b)` is not yet defined as a `PMF` in Lean; its sample space, table, and the two laws it needs
(`P4`) are. Defining it is the first task of the next slice (`P9a`).

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

**Accounting.** Bad-event terms: `2q/2^128` (step 3) + `2q₁/2^128 + 2q₂/2^128` (steps 5–6) +
the `(x7,0)` reparametrization points (already inside the per-index count of step 5). So
`advantage ≤ 4q/2^128 + ε₀`, i.e. **K = 4**, with
`ε₀ ≤ 2·1270·2^-131 + 3/p < 2^-119`. `workPerAdvantage_of_le` (proved) closes the obligation from
`K ≤ 2^28` and `ε₀ ≤ 2^-101`; the margin to the wall is `2^26`.

Two things the slice-3b analysis had that this chain does **not** need: hiding all 1270
unselected-label values by an explicit shift (absorbed by `P4`), and the `(2^128 − q)`
denominators (the `R`-side bounds sample the hidden label fresh, so each log entry hits with
probability exactly `k/2^128`).

## 5. Lemma list, dependencies, status

| id | content | file / name | status |
|---|---|---|---|
| P1 | programming involution `(π, r) ↦ (π programmed at ℓ to r, π ℓ)`; uniform `π` = uniform `π°` programmed at fresh uniform `r`; family version over `FixedKeyIndex` | `Proof/Programming.lean`: `programAt`, `programAtEquiv`, `uniform_programAt`, `programFamily`, `uniform_programFamily` | **done** |
| P2 | deterministic identical-until-bad for logged runs: same log, views agreeing off `bad` ⇒ same `(result, log)` law on good logs; bind form of `identical_until_bad`; log monotone, log length ≤ initial + budget | `Proof/Logged.lean`: `run_idealOracle_agree`, `bind_identical_until_bad`, `run_idealOracle_log_mono`, `run_idealOracle_log_length` | **done** |
| P3 | independence bad-bounds: if the log is a function of data independent of a uniform label `ℓ`, `P[log hits k points determined by ℓ] ≤ k·|log|/2^128`; needs `bind_comm` to sample `ℓ` (and `ρ ⊕ ℓ`) after the run, then a union bound over the log entries | — | open |
| P4 | static bijection raw ↔ middle; `c0` affine in `mask`; visible law uniform off-curve, shift law on-curve | `Proof/Reference.lean`: `middleEquiv`, `Coordinates.table_c0_eq`, `visibleCoordinates_offCurve`, `visibleCoordinates_onCurve` | **done** |
| P5 | bind-swap: if stage 1 depends only on `view₁(ω)` and, for every `inp`, `map (ω ↦ (view₁ ω, rest inp ω)) μ = bind μ₁ (v ↦ map (v, ·) (ν inp v))`, then `bind μ (ω ↦ stage1 (view₁ ω) >>= r ↦ stage2 (view₁ ω) (rest r.inp ω) r) = bind μ₁ (v ↦ stage1 v >>= r ↦ bind (ν r.inp v) (o ↦ stage2 v o r))` (`ENNReal.tsum_comm`) | — | open |
| P6 | TV facts: `U(F*)` vs `U(F)` = `1/p`; 384-bit uniform vs (`U(F)` then `uniformHashFiber`) ≤ `p/2^384` via `Nat.count_modEq_card`; product/bind subadditivity from VCVio `tvDist_bind_left_le`/`tvDist_bind_right_le`/`tvDist_map_le` | — | open |
| P7 | `steer` in deferred form: on-curve `wanted = o x7 0 + (c/s − u)`; the hash branch equals `R`'s programming at `(x7,0)` after `π° ↦ swap(r₁,r₂)∘π°`; the pad branch equals `R`'s pad programming | uses `Proof/Steering.lean` (`steer_release`, `decrypt_programmed`, `hashToField_programmed`) | open |
| P8 | arithmetic tail `ε ≤ K q/2^128 + ε₀`, `K ≤ 2^28`, `ε₀ ≤ 2^-101` ⇒ `WorkPerAdvantage 100 (q+1) ε`; `advantage ≤ 1` | `Proof/Reference.lean`: `workPerAdvantage_of_le`, `advantage_le_one` | **done** |
| P9a | define `R(b)` as a `PMF Bool` (state `State`, handler `idealOracle`, programming at selected labels with `programAll`, fiber samples for bit-0 gates) | — | open |
| P9b | unfold `idealGame` for `hybridSimulator` and `simulator` into the shape of §4 (as `hybridGame_eq_core` does), marginalize unused tape fields (`uniform_bind_setBridge` pattern) | `Proof/Privacy.lean` has the hybrid half | open |
| P10 | assemble §4 with `advantageTriangle` / `event_difference_le` and P8 | — | open |

Dependencies: P9a needs P4's definitions; P3 needs P2 (log length) and P9a; P5 needs P4; P7 needs
P1 and P9a; P10 needs everything. Generic helpers are in `Proof/Uniform.lean`
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
