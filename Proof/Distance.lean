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
    (by simp)

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

/-! ### The hash fiber law -/

theorem baseFieldModulus_nat_pos : 0 < baseFieldModulus := by decide

theorem baseFieldModulus_lt_digests : baseFieldModulus < 2 ^ 384 := by decide

/-- The number of complete residue blocks of the modulus inside the digest space. -/
def fiberBlocks : Nat := 2 ^ 384 / baseFieldModulus

theorem fiberBlocks_pos : 0 < fiberBlocks :=
  Nat.div_pos (le_of_lt baseFieldModulus_lt_digests) baseFieldModulus_nat_pos

theorem fiberValue_lt (target : BaseField) (step : Fin fiberBlocks) :
    target.val + step.val * baseFieldModulus < 2 ^ 384 := by
  have blocks : (step.val + 1) * baseFieldModulus ≤ 2 ^ 384 :=
    (Nat.le_div_iff_mul_le baseFieldModulus_nat_pos).mp step.isLt
  have small : target.val < baseFieldModulus := target.val_lt
  calc target.val + step.val * baseFieldModulus
      < baseFieldModulus + step.val * baseFieldModulus := by omega
    _ = (step.val + 1) * baseFieldModulus := by ring
    _ ≤ 2 ^ 384 := blocks

/-- The residue blocks list distinct members of one fiber. -/
def fiberElement (target : BaseField) (step : Fin fiberBlocks) : HashFiber target :=
  ⟨BitVec.ofNat 384 (target.val + step.val * baseFieldModulus), by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (fiberValue_lt target step), Nat.cast_add,
      Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val]⟩

theorem fiberElement_toNat (target : BaseField) (step : Fin fiberBlocks) :
    (fiberElement target step).val.toNat = target.val + step.val * baseFieldModulus := by
  simp only [fiberElement]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (fiberValue_lt target step)]

theorem fiberElement_injective (target : BaseField) :
    Function.Injective (fiberElement target) := by
  intro first second equal
  have values : target.val + first.val * baseFieldModulus =
      target.val + second.val * baseFieldModulus := by
    rw [← fiberElement_toNat target first, ← fiberElement_toNat target second, equal]
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right baseFieldModulus_nat_pos
    (Nat.add_left_cancel values))

/-- Every member of a fiber sits in one residue block. -/
def fiberIndex (target : BaseField) (element : HashFiber target) : Fin (fiberBlocks + 1) :=
  ⟨element.val.toNat / baseFieldModulus,
    Nat.lt_succ_of_le (Nat.div_le_div_right (le_of_lt element.val.isLt))⟩

theorem fiberIndex_injective (target : BaseField) :
    Function.Injective (fiberIndex target) := by
  have residue : ∀ element : HashFiber target,
      element.val.toNat % baseFieldModulus = target.val := by
    intro element
    conv_rhs => rw [← element.property]
    rw [ZMod.val_natCast]
  intro first second equal
  have quotients : first.val.toNat / baseFieldModulus = second.val.toNat / baseFieldModulus :=
    congrArg Fin.val equal
  refine Subtype.ext (BitVec.eq_of_toNat_eq ?_)
  have firstSplit := Nat.div_add_mod first.val.toNat baseFieldModulus
  have secondSplit := Nat.div_add_mod second.val.toNat baseFieldModulus
  rw [residue first] at firstSplit
  rw [residue second] at secondSplit
  calc first.val.toNat
      = baseFieldModulus * (first.val.toNat / baseFieldModulus) + target.val := firstSplit.symm
    _ = baseFieldModulus * (second.val.toNat / baseFieldModulus) + target.val := by
        rw [quotients]
    _ = second.val.toNat := secondSplit

theorem le_card_hashFiber (target : BaseField) :
    fiberBlocks ≤ Fintype.card (HashFiber target) := by
  simpa using Fintype.card_le_of_injective (fiberElement target) (fiberElement_injective target)

theorem card_hashFiber_le (target : BaseField) :
    Fintype.card (HashFiber target) ≤ fiberBlocks + 1 := by
  simpa using Fintype.card_le_of_injective (fiberIndex target) (fiberIndex_injective target)

theorem card_hashFiber_pos (target : BaseField) : 0 < Fintype.card (HashFiber target) :=
  lt_of_lt_of_le fiberBlocks_pos (le_card_hashFiber target)

/-- Every fiber is at least one residue block short of the average size. -/
theorem card_hashFiber_lower (target : BaseField) :
    2 ^ 384 ≤ baseFieldModulus * Fintype.card (HashFiber target) + baseFieldModulus := by
  have split := Nat.div_add_mod (2 ^ 384) baseFieldModulus
  have remainder : 2 ^ 384 % baseFieldModulus < baseFieldModulus :=
    Nat.mod_lt _ baseFieldModulus_nat_pos
  have blocks : baseFieldModulus * fiberBlocks ≤
      baseFieldModulus * Fintype.card (HashFiber target) :=
    Nat.mul_le_mul_left _ (le_card_hashFiber target)
  unfold fiberBlocks at blocks
  omega

/-- Every fiber is at most one residue block above the average size. -/
theorem card_hashFiber_upper (target : BaseField) :
    baseFieldModulus * Fintype.card (HashFiber target) ≤ 2 ^ 384 + baseFieldModulus := by
  have blocks : baseFieldModulus * fiberBlocks ≤ 2 ^ 384 := by
    unfold fiberBlocks
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  calc baseFieldModulus * Fintype.card (HashFiber target)
      ≤ baseFieldModulus * (fiberBlocks + 1) :=
        Nat.mul_le_mul_left _ (card_hashFiber_le target)
    _ = baseFieldModulus * fiberBlocks + baseFieldModulus := by rw [Nat.mul_succ]
    _ ≤ 2 ^ 384 + baseFieldModulus := Nat.add_le_add_right blocks _

theorem card_bitVec_384 : Fintype.card (BitVec 384) = 2 ^ 384 :=
  (Fintype.card_congr
    (BitVec.equivFin : BitVec 384 ≃+* Fin (2 ^ 384)).toEquiv).trans (Fintype.card_fin _)

/-- The uniform sample of one fiber, at one digest. -/
theorem uniformHashFiber_apply (target : BaseField) (hash : BitVec 384) :
    uniformHashFiber target hash =
      if ((hash.toNat : BaseField) = target) then
        (Fintype.card (HashFiber target) : ENNReal)⁻¹ else 0 := by
  unfold uniformHashFiber
  rw [PMF.map_apply, tsum_fintype]
  split
  · rename_i member
    rw [Finset.sum_eq_single (⟨hash, member⟩ : HashFiber target)]
    · rw [if_pos rfl, PMF.uniformOfFintype_apply]
    · intro element _ different
      rw [if_neg]
      intro equal
      exact different (Subtype.ext equal.symm)
    · intro absent
      exact absurd (Finset.mem_univ _) absent
  · rename_i notMember
    refine Finset.sum_eq_zero fun element _ => ?_
    rw [if_neg]
    intro equal
    subst equal
    exact notMember element.property

/-- A uniform field element followed by a uniform sample of its fiber, at one digest. -/
theorem uniform_bind_hashFiber_apply (hash : BitVec 384) :
    ((PMF.uniformOfFintype BaseField).bind uniformHashFiber) hash =
      (baseFieldModulus : ENNReal)⁻¹ *
        (Fintype.card (HashFiber ((hash.toNat : BaseField))) : ENNReal)⁻¹ := by
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single ((hash.toNat : BaseField))]
  · rw [PMF.uniformOfFintype_apply, ZMod.card, uniformHashFiber_apply, if_pos rfl]
  · intro target _ different
    rw [uniformHashFiber_apply, if_neg fun equal => different equal.symm, mul_zero]
  · intro absent
    exact absurd (Finset.mem_univ _) absent

/-- The difference the fiber law makes at one field element. -/
def fiberTerm (target : BaseField) : ℝ :=
  |1 / ((baseFieldModulus : ℝ) * (Fintype.card (HashFiber target) : ℝ)) - 1 / 2 ^ 384|

/-- A count within one modulus of the average fiber size contributes at most the mass of one
digest. -/
theorem count_mul_difference_le {digests modulus count : ℝ} (digestsPos : 0 < digests)
    (modulusPos : 0 < modulus) (countPos : 0 < count)
    (lower : digests ≤ modulus * count + modulus)
    (upper : modulus * count ≤ digests + modulus) :
    count * |1 / (modulus * count) - 1 / digests| ≤ 1 / digests := by
  have modulusNe : modulus ≠ 0 := modulusPos.ne'
  have countNe : count ≠ 0 := countPos.ne'
  have digestsNe : digests ≠ 0 := digestsPos.ne'
  have expand : 1 / (modulus * count) - 1 / digests =
      (digests - modulus * count) / (modulus * count * digests) := by
    field_simp
  have cancel : count * (|digests - modulus * count| / (modulus * count * digests)) =
      |digests - modulus * count| / (modulus * digests) := by
    field_simp
  have absBound : |digests - modulus * count| ≤ modulus :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [expand, abs_div, abs_of_pos (show (0 : ℝ) < modulus * count * digests by positivity),
    cancel]
  calc |digests - modulus * count| / (modulus * digests)
      ≤ modulus / (modulus * digests) := by gcongr
    _ = 1 / digests := by field_simp

/-- One fiber contributes at most the mass of one digest. -/
theorem card_mul_fiberTerm_le (target : BaseField) :
    (Fintype.card (HashFiber target) : ℝ) * fiberTerm target ≤ 1 / 2 ^ 384 := by
  have cardPos : (0 : ℝ) < (Fintype.card (HashFiber target) : ℝ) := by
    exact_mod_cast card_hashFiber_pos target
  have lower : (2 : ℝ) ^ 384 ≤
      (baseFieldModulus : ℝ) * (Fintype.card (HashFiber target) : ℝ) + baseFieldModulus := by
    exact_mod_cast card_hashFiber_lower target
  have upper : (baseFieldModulus : ℝ) * (Fintype.card (HashFiber target) : ℝ) ≤
      (2 : ℝ) ^ 384 + baseFieldModulus := by
    exact_mod_cast card_hashFiber_upper target
  exact count_mul_difference_le (by positivity) baseFieldModulus_pos cardPos lower upper

/-- A uniform digest and a uniform field element followed by a uniform sample of its fiber
differ in total by at most `p / 2 ^ 384`. -/
theorem hashFiber_total_difference :
    totalDifference ((PMF.uniformOfFintype BaseField).bind uniformHashFiber)
        (PMF.uniformOfFintype (BitVec 384)) ≤ (baseFieldModulus : ℝ) / 2 ^ 384 := by
  have term : ∀ hash : BitVec 384,
      |(((PMF.uniformOfFintype BaseField).bind uniformHashFiber) hash).toReal -
          ((PMF.uniformOfFintype (BitVec 384)) hash).toReal| =
        fiberTerm ((hash.toNat : BaseField)) := by
    intro hash
    have mixture : (((PMF.uniformOfFintype BaseField).bind uniformHashFiber) hash).toReal =
        1 / ((baseFieldModulus : ℝ) *
          (Fintype.card (HashFiber ((hash.toNat : BaseField))) : ℝ)) := by
      rw [uniform_bind_hashFiber_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div, mul_inv]
    have digest : ((PMF.uniformOfFintype (BitVec 384)) hash).toReal = 1 / 2 ^ 384 := by
      rw [PMF.uniformOfFintype_apply, card_bitVec_384, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, one_div, Nat.cast_pow, Nat.cast_ofNat]
    rw [mixture, digest, fiberTerm]
  unfold totalDifference
  rw [Finset.sum_congr rfl fun hash _ => term hash,
    ← Fintype.sum_fiberwise' (fun hash : BitVec 384 => ((hash.toNat : BaseField))) fiberTerm]
  have inner : ∀ target : BaseField,
      (∑ _element : HashFiber target, fiberTerm target) ≤ 1 / 2 ^ 384 := by
    intro target
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact card_mul_fiberTerm_le target
  calc ∑ target : BaseField, ∑ _element : HashFiber target, fiberTerm target
      ≤ ∑ _target : BaseField, (1 : ℝ) / 2 ^ 384 :=
        Finset.sum_le_sum fun target _ => inner target
    _ = (baseFieldModulus : ℝ) / 2 ^ 384 := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one_div]

end

end Kriterion.ArgoMAC.Security
