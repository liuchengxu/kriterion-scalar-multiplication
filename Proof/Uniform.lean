/-
This file collects the generic uniform-sampling facts that the privacy proof
uses: two finite-type instances give one uniform law, a bijection preserves a
uniform sample, two independent uniform samples are one uniform sample of the
product, and a bind may be rewritten on the support of the sampled law.
-/

import Proof.Finite

namespace Kriterion.ArgoMAC.Security

noncomputable section

/-! ### Uniform sampling facts -/

/-- Two finite-type instances give the same uniform law. -/
theorem uniformOfFintype_congr {Value : Type} (first second : Fintype Value) [Nonempty Value] :
    @PMF.uniformOfFintype Value first _ = @PMF.uniformOfFintype Value second _ := by
  cases Subsingleton.elim first second
  rfl

/-- A uniform sample composed with a bijection is a uniform sample. -/
theorem uniformOfFintype_bind_equiv {Value Result : Type} [Fintype Value] [Nonempty Value]
    (bijection : Value ≃ Value) (continuation : Value → PMF Result) :
    ((PMF.uniformOfFintype Value).bind fun value => continuation (bijection value)) =
      (PMF.uniformOfFintype Value).bind continuation := by
  ext result
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  exact bijection.sum_comp fun value => (Fintype.card Value : ENNReal)⁻¹ * continuation value result

/-- Two independent uniform samples are one uniform sample of the product. -/
theorem uniformOfFintype_bind_prod {Left Right Result : Type} [Fintype Left] [Nonempty Left]
    [Fintype Right] [Nonempty Right] (continuation : Left → Right → PMF Result) :
    ((PMF.uniformOfFintype Left).bind fun left =>
        (PMF.uniformOfFintype Right).bind fun right => continuation left right) =
      (PMF.uniformOfFintype (Left × Right)).bind fun pair => continuation pair.1 pair.2 := by
  ext result
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_fintype, Fintype.sum_prod_type,
    Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [Finset.mul_sum, mul_assoc]

/-- A bind may be rewritten on the support of the sampled law. -/
theorem bind_congr_support {Value Result : Type} {law : PMF Value}
    {first second : Value → PMF Result}
    (agree : ∀ value ∈ law.support, first value = second value) :
    law.bind first = law.bind second := by
  ext result
  simp only [PMF.bind_apply]
  refine tsum_congr fun value => ?_
  by_cases member : value ∈ law.support
  · rw [agree value member]
  · rw [(law.apply_eq_zero_iff value).mpr member, zero_mul, zero_mul]

/-- A uniform sample mapped through a bijection is a uniform sample. -/
theorem uniformOfFintype_map_equiv {Value : Type} [Fintype Value] [Nonempty Value]
    (bijection : Value ≃ Value) :
    (PMF.uniformOfFintype Value).map bijection = PMF.uniformOfFintype Value := by
  rw [PMF.map, Function.comp_def, uniformOfFintype_bind_equiv bijection PMF.pure, PMF.bind_pure]

end

end Kriterion.ArgoMAC.Security
