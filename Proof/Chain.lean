/-
This file holds the assembly layer of the chain of games: the three ways one
hop can cost advantage, and the arithmetic of the accounting.

A hop either swaps the sampled law (its cost is the total difference of the two
laws), or swaps the continuation (its cost is the largest pointwise
advantage), or is identical until a bad event (its cost is the mass of the bad
event). The chain's ten identical-until-bad hops each cost `2 q / 2 ^ 128`, and
the one-time terms -- the mask law, the 1270 digest replacements and the
freshness of the two chunks the steering reparametrisation swaps -- together
stay below `2 ^ -119`, far below the `2 ^ -101` the arithmetic tail needs.
-/

import Proof.Distance

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

noncomputable section

/-! ### The three kinds of hop -/

theorem advantage_eq (first second : PMF Bool) :
    advantage first second = |(first true).toReal - (second true).toReal| := rfl

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

/-- An identical-until-bad hop whose bad event depends on the outcome as well as on the
sample. Each hop of the chain swaps a stage's oracle view, and the queries that see the
swap are the entries of the run's own log, so the bad event is not a property of the
sample alone. It costs the mass of the bad event under the joint law of the second game. -/
theorem advantage_bind_map_le_jointBad {Sample Outcome : Type} (law : PMF Sample)
    (first second : Sample → PMF Outcome) (project : Outcome → Bool)
    (bad : Set (Sample × Outcome))
    (agree : ∀ pair ∉ bad, first pair.1 pair.2 = second pair.1 pair.2) :
    advantage ((law.bind first).map project) ((law.bind second).map project) ≤
      ((jointLaw law second).toOuterMeasure bad).toReal := by
  have joint := Probability.identical_until_bad (jointLaw law first) (jointLaw law second) bad
    (Prod.snd ⁻¹' (project ⁻¹' ({true} : Set Bool))) (by
      rintro ⟨sample, outcome⟩ good
      rw [jointLaw_apply, jointLaw_apply, agree (sample, outcome) good])
  have expand (continuation : Sample → PMF Outcome) :
      ((law.bind continuation).map project) true =
        (jointLaw law continuation).toOuterMeasure
          (Prod.snd ⁻¹' (project ⁻¹' ({true} : Set Bool))) := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      ← jointLaw_map_snd law continuation, PMF.toOuterMeasure_map_apply]
  rw [advantage_eq, expand first, expand second]
  exact joint

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

/-- The one-time terms of the chain: the uniform nonzero mask against the uniform field
mask, the digest replacement of all 1270 gates, and the freshness of the two chunks the
steering reparametrisation swaps. -/
def chainOneTime : ℝ :=
  2 / (baseFieldModulus : ℝ) + 1270 * ((baseFieldModulus : ℝ) / 2 ^ 384) + 6 / 2 ^ 128

/-- The one-time terms stay below `2 ^ -119`. -/
theorem chainOneTime_lt : chainOneTime < 1 / 2 ^ 119 := by
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
  unfold chainOneTime
  calc 2 / (baseFieldModulus : ℝ) + 1270 * ((baseFieldModulus : ℝ) / 2 ^ 384) + 6 / 2 ^ 128
      ≤ 1 / 2 ^ 130 + 1270 / 2 ^ 130 + 6 / 2 ^ 128 :=
        add_le_add (add_le_add maskLe digestsLe) le_rfl
    _ < 1 / 2 ^ 119 := by norm_num

theorem chainOneTime_le : chainOneTime ≤ 1 / 2 ^ 101 :=
  le_of_lt (lt_of_lt_of_le chainOneTime_lt (by norm_num))

/-- The chain closes the obligation: ten identical-until-bad hops, each costing
`2 q / 2 ^ 128` over the whole log, plus the one-time terms. -/
theorem workPerAdvantage_of_chain (adversary : Adversary) (parameter : Nat) (error : ℝ)
    (bound : error ≤ 10 * ((adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 + chainOneTime) :
    WorkPerAdvantage 100 (adversaryWork adversary parameter) error := by
  unfold adversaryWork
  exact workPerAdvantage_of_le (adversary.firstQueryBudget parameter +
    adversary.secondQueryBudget parameter) 10 chainOneTime error (by norm_num)
    chainOneTime_le bound

end

end Kriterion.ArgoMAC.Security
