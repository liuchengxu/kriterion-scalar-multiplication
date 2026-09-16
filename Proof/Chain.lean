/-
This file holds the assembly layer of the chain of games: the three ways one
hop can cost advantage, and the arithmetic of the accounting.

A hop either swaps the sampled law (its cost is the total difference of the two
laws), or swaps the continuation (its cost is the largest pointwise
advantage), or is identical until a bad event (its cost is the mass of the bad
event). Eight of the chain's identical-until-bad hops cost `2 q / 2 ^ 128` each
(four on the hybrid side, four on the simulated side) and the steering hop costs
`8 q / 2 ^ 128`, so the per-query constant is `16`; the one-time terms -- the mask
law and the 1270 digest replacements on each side, plus the freshness of the two
chunks the steering reparametrisation swaps -- together stay below `2 ^ -118`, far
below the `2 ^ -101` the arithmetic tail needs.
-/

import Proof.Distance

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

noncomputable section

/-! ### The three kinds of hop -/

theorem advantage_eq (first second : PMF Bool) :
    advantage first second = |(first true).toReal - (second true).toReal| := rfl

/-- Advantage is symmetric, so a hop proved in one orientation closes the other. -/
theorem advantage_comm (first second : PMF Bool) :
    advantage first second = advantage second first := by
  rw [advantage_eq, advantage_eq, abs_sub_comm]

/-- An identical-until-bad hop costs the mass of the bad event. -/
theorem advantage_bind_le_bad {Sample : Type} (first second : PMF Sample)
    (firstContinuation secondContinuation : Sample → PMF Bool) (bad : Set Sample)
    (agreeLaw : ∀ sample ∉ bad, first sample = second sample)
    (agreeContinuation : ∀ sample ∉ bad, firstContinuation sample = secondContinuation sample) :
    advantage (first.bind firstContinuation) (second.bind secondContinuation) ≤
      (second.toOuterMeasure bad).toReal := by
  have base := bind_identical_until_bad first second firstContinuation secondContinuation bad
    {true} agreeLaw agreeContinuation
  rwa [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at base

/-- An identical-until-bad hop whose bad event depends on the outcome of the differing
step as well as on the sample. Each hop of the chain swaps one stage's oracle view, and
the queries that see the swap are the entries of that stage's own log, so the bad event is
not a property of the sample alone. The hop costs the mass of the bad event under the
joint law of the second game. -/
theorem advantage_bind_le_jointBad {Sample Outcome : Type} (law : PMF Sample)
    (first second : Sample → PMF Outcome) (continuation : Sample → Outcome → PMF Bool)
    (bad : Set (Sample × Outcome))
    (agree : ∀ pair ∉ bad, first pair.1 pair.2 = second pair.1 pair.2) :
    advantage (law.bind fun sample => (first sample).bind (continuation sample))
        (law.bind fun sample => (second sample).bind (continuation sample)) ≤
      ((jointLaw law second).toOuterMeasure bad).toReal := by
  have factor (step : Sample → PMF Outcome) :
      (law.bind fun sample => (step sample).bind (continuation sample)) =
        (jointLaw law step).bind fun pair => continuation pair.1 pair.2 := by
    unfold jointLaw
    rw [PMF.bind_bind]
    refine congrArg (PMF.bind law) (funext fun sample => ?_)
    rw [PMF.bind_map]
    rfl
  rw [factor first, factor second]
  refine advantage_bind_le_bad (jointLaw law first) (jointLaw law second) _ _ bad ?_
    fun _ _ => rfl
  rintro ⟨sample, outcome⟩ good
  rw [jointLaw_apply, jointLaw_apply, agree (sample, outcome) good]

/-- Swapping the sampled law of a game costs the total difference of the two laws. -/
theorem advantage_bind_le_totalDifference {Sample : Type} [Fintype Sample]
    (first second : PMF Sample) (continuation : Sample → PMF Bool) :
    advantage (first.bind continuation) (second.bind continuation) ≤
      totalDifference first second :=
  bind_apply_sub_le first second continuation true

/-- Swapping the continuation of a game costs the largest pointwise advantage. -/
theorem advantage_bind_le_of_le {Sample : Type} [Fintype Sample] (law : PMF Sample)
    (first second : Sample → PMF Bool) (bound : ℝ)
    (pointwise : ∀ sample, advantage (first sample) (second sample) ≤ bound) :
    advantage (law.bind first) (law.bind second) ≤ bound :=
  bind_apply_sub_le_of_le law first second true bound pointwise

/-- Two hops cost the sum of their bounds. -/
theorem advantage_trans (first middle last : PMF Bool) (firstStep lastStep : ℝ)
    (firstLe : advantage first middle ≤ firstStep)
    (lastLe : advantage middle last ≤ lastStep) :
    advantage first last ≤ firstStep + lastStep :=
  (advantageTriangle first middle last).trans (add_le_add firstLe lastLe)

/-! ### The accounting -/

theorem baseFieldModulus_le : (baseFieldModulus : ℝ) ≤ 2 ^ 254 := by
  have bound : (baseFieldModulus : ℝ) ≤ ((2 ^ 254 : Nat) : ℝ) := Nat.cast_le.mpr (by decide)
  rwa [Nat.cast_pow, Nat.cast_ofNat] at bound

theorem baseFieldModulus_ge : (2 : ℝ) ^ 253 ≤ (baseFieldModulus : ℝ) := by
  have bound : ((2 ^ 253 : Nat) : ℝ) ≤ (baseFieldModulus : ℝ) := Nat.cast_le.mpr (by decide)
  rwa [Nat.cast_pow, Nat.cast_ofNat] at bound

/-- The one-time terms of **one** side of the chain: the uniform nonzero mask against the
uniform field mask, and the digest replacement of all 1270 gates. Both the hybrid side and
the simulated side pay this, because each side replaces the fresh secrets of its own
reparametrisation by the reference game's coordinates. -/
def sideOneTime : ℝ :=
  2 / (baseFieldModulus : ℝ) + 1270 * ((baseFieldModulus : ℝ) / 2 ^ 384)

/-- The one-time terms of the chain: one `sideOneTime` for the hybrid side, one for the
simulated side, and the freshness of the two chunks the steering reparametrisation swaps. -/
def chainOneTime : ℝ := sideOneTime + sideOneTime + 6 / 2 ^ 128

/-- The one-time terms stay below `2 ^ -118`. -/
theorem chainOneTime_lt : chainOneTime < 1 / 2 ^ 118 := by
  have modulusPos : (0 : ℝ) < baseFieldModulus :=
    lt_of_lt_of_le (by positivity) baseFieldModulus_ge
  have maskLe : 2 / (baseFieldModulus : ℝ) ≤ 1 / 2 ^ 130 := by
    rw [div_le_div_iff₀ modulusPos (by positivity)]
    calc (2 : ℝ) * 2 ^ 130 = 2 ^ 131 := by ring
      _ ≤ 2 ^ 253 := by norm_num
      _ ≤ (baseFieldModulus : ℝ) := baseFieldModulus_ge
      _ = 1 * (baseFieldModulus : ℝ) := (one_mul _).symm
  have digestsLe : 1270 * ((baseFieldModulus : ℝ) / 2 ^ 384) ≤ 1270 / 2 ^ 130 := by
    have step : (baseFieldModulus : ℝ) / 2 ^ 384 ≤ 1 / 2 ^ 130 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc (baseFieldModulus : ℝ) * 2 ^ 130 ≤ 2 ^ 254 * 2 ^ 130 :=
            mul_le_mul_of_nonneg_right baseFieldModulus_le (by positivity)
        _ = 1 * 2 ^ 384 := by rw [one_mul, ← pow_add]
    calc 1270 * ((baseFieldModulus : ℝ) / 2 ^ 384) ≤ 1270 * (1 / 2 ^ 130) :=
          mul_le_mul_of_nonneg_left step (by norm_num)
      _ = 1270 / 2 ^ 130 := by ring
  have sideLe : sideOneTime ≤ 1 / 2 ^ 130 + 1270 / 2 ^ 130 := add_le_add maskLe digestsLe
  unfold chainOneTime
  calc sideOneTime + sideOneTime + 6 / 2 ^ 128
      ≤ (1 / 2 ^ 130 + 1270 / 2 ^ 130) + (1 / 2 ^ 130 + 1270 / 2 ^ 130) + 6 / 2 ^ 128 :=
        add_le_add (add_le_add sideLe sideLe) le_rfl
    _ < 1 / 2 ^ 118 := by norm_num

theorem chainOneTime_le : chainOneTime ≤ 1 / 2 ^ 101 :=
  le_of_lt (lt_of_lt_of_le chainOneTime_lt (by norm_num))

/-- The per-query constant of the chain.

Eight hops are bounded on a *label* the adversary has not been handed, and each such hop
hides two points per query direction, so each costs `2 q / 2 ^ 128`: the hybrid side's
step 3 (two hops) and its two halves of step 2's identification, and the simulated side's
steps 5 and 6 -- `4 q / 2 ^ 128` per side, `8 q / 2 ^ 128` for the two sides that are
already machine-checked (`advantage_hybridGame_referenceGame_le` and
`advantage_simulatedGame_steeredReferenceGame_le` each supply `4 q / 2 ^ 128`).

The steering hop is **not** bounded on a label: three of its four bad points are hit only
by evaluating or inverting the *unprogrammed* permutation at a point the transcript has
not pinned, and conditionally on the transcript each of those is uniform over at least
`2 ^ 128 - q` values; the fourth is a guess of one 128-bit chunk of a hash-fiber sample,
whose largest point mass is above `1 / 2 ^ 128` because the fiber has about
`2 ^ 384 / p` elements, not a power of two. Charging `1 / (2 ^ 128 - q) ≤ 2 / 2 ^ 128` for
the first three (legitimate for `q < 2 ^ 127`; for `q ≥ 2 ^ 127` the whole bound is free,
since `8 q / 2 ^ 128 ≥ 4 ≥ 1` and every advantage is at most one) and `2 / 2 ^ 128` for
the fourth gives `8 q / 2 ^ 128` for the hop.

So `8 + 8 = 16`. `workPerAdvantage_of_le` proves the arithmetic tail for **any**
`perQuery ≤ 2 ^ 28`, so the margin to the wall is still `2 ^ 24`; `16` is chosen with
slack over the honest figure (about `12.2`) rather than tight, and no statement of the
obligation depends on the value. -/
def chainPerQuery : ℝ := 16

/-- The chain closes the obligation: the hops of the two sides at `2 q / 2 ^ 128` each and
the steering hop at `8 q / 2 ^ 128`, plus the one-time terms. -/
theorem workPerAdvantage_of_chain (adversary : Adversary) (parameter : Nat) (error : ℝ)
    (bound : error ≤ chainPerQuery * ((adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 + chainOneTime) :
    WorkPerAdvantage 100 (adversaryWork adversary parameter) error := by
  unfold adversaryWork
  exact workPerAdvantage_of_le (adversary.firstQueryBudget parameter +
    adversary.secondQueryBudget parameter) chainPerQuery chainOneTime error
    (by unfold chainPerQuery; norm_num) chainOneTime_le bound

end

end Kriterion.ArgoMAC.Security
