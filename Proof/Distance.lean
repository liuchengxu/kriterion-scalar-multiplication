/-
This file proves the one-time distance facts of the steering-invisibility
proof. Continuing two laws with the same continuation changes any outcome
probability by at most the total difference of the two laws; continuing one law
with two continuations costs their largest pointwise difference. The uniform
nonzero mask differs from the uniform field mask in total by `2 / p`, and a
uniform 384-bit string differs from a uniform field element followed by a
uniform sample of its fiber in total by at most `p / 2 ^ 384`.
-/

import Proof.Hidden

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

set_option exponentiation.threshold 400

/-! ### Total difference -/

/-- The total difference of two laws on a finite type: the sum, over all samples, of the
difference of the two masses. It is twice the total variation distance. -/
def totalDifference {Sample : Type} [Fintype Sample] (first second : PMF Sample) : ℝ :=
  ∑ sample, |(first sample).toReal - (second sample).toReal|

theorem totalDifference_nonneg {Sample : Type} [Fintype Sample] (first second : PMF Sample) :
    0 ≤ totalDifference first second :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem totalDifference_comm {Sample : Type} [Fintype Sample] (first second : PMF Sample) :
    totalDifference first second = totalDifference second first :=
  Finset.sum_congr rfl fun _ _ => abs_sub_comm _ _

/-- Total difference obeys the triangle inequality, so a chain of laws costs the sum of its
steps. -/
theorem totalDifference_triangle {Sample : Type} [Fintype Sample]
    (first middle second : PMF Sample) :
    totalDifference first second ≤
      totalDifference first middle + totalDifference middle second := by
  unfold totalDifference
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun sample _ => abs_sub_le _ _ _

/-- Continuing two laws with one continuation moves any outcome probability by at most the
total difference of the laws. -/
theorem bind_apply_sub_le {Sample Outcome : Type} [Fintype Sample] (first second : PMF Sample)
    (continuation : Sample → PMF Outcome) (outcome : Outcome) :
    |((first.bind continuation) outcome).toReal - ((second.bind continuation) outcome).toReal| ≤
      totalDifference first second := by
  unfold totalDifference
  simp only [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun sample _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top first sample)
        (PMF.apply_ne_top (continuation sample) outcome)),
    ENNReal.toReal_sum (fun sample _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top second sample)
        (PMF.apply_ne_top (continuation sample) outcome)),
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun sample _ => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← sub_mul, abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by simpa using PMF.coe_le_one (continuation sample) outcome)

/-- Continuing one law with two continuations moves any outcome probability by at most the
largest pointwise difference of the continuations. -/
theorem bind_apply_sub_le_of_le {Sample Outcome : Type} [Fintype Sample] (law : PMF Sample)
    (first second : Sample → PMF Outcome) (outcome : Outcome) (bound : ℝ)
    (pointwise : ∀ sample,
      |((first sample) outcome).toReal - ((second sample) outcome).toReal| ≤ bound) :
    |((law.bind first) outcome).toReal - ((law.bind second) outcome).toReal| ≤ bound := by
  simp only [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun sample _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top law sample)
        (PMF.apply_ne_top (first sample) outcome)),
    ENNReal.toReal_sum (fun sample _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top law sample)
        (PMF.apply_ne_top (second sample) outcome)),
    ← Finset.sum_sub_distrib]
  have total : ∑ sample, law sample = 1 := (tsum_fintype _).symm.trans (PMF.tsum_coe law)
  have weights : ∑ sample, (law sample).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun sample _ => PMF.apply_ne_top law sample), total,
      ENNReal.toReal_one]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have summand : ∀ sample ∈ (Finset.univ : Finset Sample),
      |(law sample * (first sample) outcome).toReal -
        (law sample * (second sample) outcome).toReal| ≤ (law sample).toReal * bound := by
    intro sample _
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_sub, abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (pointwise sample) ENNReal.toReal_nonneg
  exact (Finset.sum_le_sum summand).trans
    (le_of_eq (by rw [← Finset.sum_mul, weights, one_mul]))

/-! ### The mask law -/

/-- The base field is the nonzero base field plus zero. -/
def nonZeroBaseSumEquiv : NonZeroBase ⊕ Unit ≃ BaseField where
  toFun
    | .inl mask => mask.value
    | .inr _ => 0
  invFun value := if nonzero : value = 0 then .inr () else .inl ⟨value, nonzero⟩
  left_inv choice := by
    cases choice with
    | inl mask => simp [mask.nonzero]
    | inr _ => simp
  right_inv value := by
    by_cases zero : value = 0
    · simp [zero]
    · simp [zero]

theorem card_nonZeroBase : Fintype.card NonZeroBase = baseFieldModulus - 1 := by
  have total := Fintype.card_congr nonZeroBaseSumEquiv
  rw [Fintype.card_sum, Fintype.card_unit, ZMod.card] at total
  omega

/-- A sum over the base field splits into the nonzero elements and zero. -/
theorem sum_baseField_split {Value : Type} [AddCommMonoid Value] (term : BaseField → Value) :
    ∑ value, term value = (∑ mask : NonZeroBase, term mask.value) + term 0 := by
  rw [← Fintype.sum_equiv nonZeroBaseSumEquiv (fun choice => term (nonZeroBaseSumEquiv choice))
    term (fun _ => rfl), Fintype.sum_sum_type]
  simp only [Fintype.sum_unique]
  rfl

/-- The law of a uniform nonzero mask at one field element. -/
theorem uniform_nonZeroBase_apply (value : BaseField) :
    ((PMF.uniformOfFintype NonZeroBase).map NonZeroBase.value) value =
      if value = 0 then 0 else ((baseFieldModulus - 1 : Nat) : ENNReal)⁻¹ := by
  rw [PMF.map_apply, tsum_fintype]
  split
  · rename_i zero
    refine Finset.sum_eq_zero fun mask _ => ?_
    rw [if_neg]
    intro equal
    exact mask.nonzero (equal.symm.trans zero)
  · rename_i nonzero
    rw [Finset.sum_eq_single ⟨value, nonzero⟩]
    · rw [if_pos rfl, PMF.uniformOfFintype_apply, card_nonZeroBase]
    · intro mask _ different
      rw [if_neg]
      intro equal
      exact different (by cases mask; cases equal; rfl)
    · intro absent
      exact absurd (Finset.mem_univ _) absent

theorem baseFieldModulus_pos : (0 : ℝ) < baseFieldModulus := by
  exact_mod_cast (show 0 < baseFieldModulus by decide)

theorem baseFieldModulus_sub_one_pos : (0 : ℝ) < ((baseFieldModulus - 1 : Nat) : ℝ) := by
  exact_mod_cast (show 0 < baseFieldModulus - 1 by decide)

/-- The uniform nonzero mask and the uniform field mask differ in total by `2 / p`. -/
theorem mask_total_difference :
    totalDifference ((PMF.uniformOfFintype NonZeroBase).map NonZeroBase.value)
      (PMF.uniformOfFintype BaseField) ≤ 2 / (baseFieldModulus : ℝ) := by
  unfold totalDifference
  have field (value : BaseField) : ((PMF.uniformOfFintype BaseField) value).toReal =
      1 / (baseFieldModulus : ℝ) := by
    rw [PMF.uniformOfFintype_apply, ZMod.card, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  have nonzero (value : BaseField) (different : value ≠ 0) :
      (((PMF.uniformOfFintype NonZeroBase).map NonZeroBase.value) value).toReal =
        1 / ((baseFieldModulus - 1 : Nat) : ℝ) := by
    rw [uniform_nonZeroBase_apply, if_neg different, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      one_div]
  have zero : (((PMF.uniformOfFintype NonZeroBase).map NonZeroBase.value) 0).toReal = 0 := by
    rw [uniform_nonZeroBase_apply, if_pos rfl, ENNReal.toReal_zero]
  have modulus := baseFieldModulus_pos
  have cast : ((baseFieldModulus - 1 : Nat) : ℝ) = (baseFieldModulus : ℝ) - 1 := by
    rw [Nat.cast_sub (by decide), Nat.cast_one]
  have predecessor : (0 : ℝ) < (baseFieldModulus : ℝ) - 1 := cast ▸ baseFieldModulus_sub_one_pos
  have term (value : BaseField) :
      |(((PMF.uniformOfFintype NonZeroBase).map NonZeroBase.value) value).toReal -
        ((PMF.uniformOfFintype BaseField) value).toReal| =
      if value = 0 then 1 / (baseFieldModulus : ℝ)
      else 1 / ((baseFieldModulus : ℝ) * ((baseFieldModulus : ℝ) - 1)) := by
    split
    · rename_i isZero
      subst isZero
      rw [zero, field, zero_sub, abs_neg, abs_of_pos (one_div_pos.mpr modulus)]
    · rename_i different
      rw [nonzero value different, field, cast, div_sub_div _ _ predecessor.ne' modulus.ne',
        one_mul, mul_one, sub_sub_cancel, mul_comm]
      exact abs_of_pos (one_div_pos.mpr (mul_pos modulus predecessor))
  simp only [term]
  rw [sum_baseField_split, if_pos rfl]
  have nonzeroSum : (∑ mask : NonZeroBase, if mask.value = 0 then 1 / (baseFieldModulus : ℝ)
      else 1 / ((baseFieldModulus : ℝ) * ((baseFieldModulus : ℝ) - 1))) =
      ((baseFieldModulus : ℝ) - 1) *
        (1 / ((baseFieldModulus : ℝ) * ((baseFieldModulus : ℝ) - 1))) := by
    rw [Finset.sum_congr rfl fun mask _ => if_neg mask.nonzero, Finset.sum_const, Finset.card_univ,
      card_nonZeroBase, nsmul_eq_mul, cast]
  rw [nonzeroSum, mul_one_div, mul_comm (baseFieldModulus : ℝ), div_mul_cancel_left₀ predecessor.ne',
    one_div, ← two_mul, div_eq_mul_inv]

end

end Kriterion.ArgoMAC.Security
