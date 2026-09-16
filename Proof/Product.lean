/-
This file builds the law of independent coordinates on a finite function type
and the tensorisation facts the digest replacement needs: the uniform law of a
function type is the product of the uniform coordinate laws, a product of
coordinate binds is the bind of the products, resampling one coordinate
replaces that coordinate's law, the uniform law of a coordinatewise subtype is
the product of the uniform coordinate subtype laws, and the total difference of
two products is at most the sum of the coordinate total differences.
-/

import Proof.Distance

namespace Kriterion.ArgoMAC.Security

noncomputable section

/-! ### Maps along a bijection -/

/-- A law mapped along a bijection is the law of the preimage. -/
theorem map_equiv_apply {Source Target : Type} (bijection : Source ≃ Target) (law : PMF Source)
    (target : Target) : (law.map bijection) target = law (bijection.symm target) := by
  rw [PMF.map_apply]
  refine (tsum_eq_single (bijection.symm target) ?_).trans ?_
  · intro source different
    refine if_neg fun equal => different ?_
    rw [equal, bijection.symm_apply_apply]
  · rw [if_pos (bijection.apply_symm_apply target).symm]

/-- A uniform sample mapped along a bijection is a uniform sample of the target. -/
theorem uniformOfFintype_map_bijection {Source Target : Type} [Fintype Source] [Nonempty Source]
    [Fintype Target] [Nonempty Target] (bijection : Source ≃ Target) :
    (PMF.uniformOfFintype Source).map bijection = PMF.uniformOfFintype Target := by
  ext target
  rw [map_equiv_apply, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
    Fintype.card_congr bijection]

/-- A bijection preserves the total difference of two laws. -/
theorem totalDifference_map_bijection {Source Target : Type} [Fintype Source] [Fintype Target]
    (bijection : Source ≃ Target) (first second : PMF Source) :
    totalDifference (first.map bijection) (second.map bijection) =
      totalDifference first second := by
  unfold totalDifference
  simp only [map_equiv_apply]
  exact bijection.symm.sum_comp fun source =>
    |(first source).toReal - (second source).toReal|

/-! ### The law of independent coordinates -/

section Product

variable {Index Value : Type} [Fintype Index] [DecidableEq Index] [Fintype Value]

/-- The law of independent coordinates: every coordinate is sampled from its own law. -/
def productPMF (laws : Index → PMF Value) : PMF (Index → Value) :=
  PMF.ofFintype (fun values => ∏ index, laws index (values index)) (by
    rw [← Fintype.prod_sum fun (index : Index) (value : Value) => laws index value]
    exact Finset.prod_eq_one fun index _ =>
      (tsum_fintype _).symm.trans (PMF.tsum_coe (laws index)))

theorem productPMF_apply (laws : Index → PMF Value) (values : Index → Value) :
    productPMF laws values = ∏ index, laws index (values index) := rfl

/-- The coordinate masses of a product law sum to one. -/
theorem sum_toReal_productPMF (laws : Index → PMF Value) :
    ∑ values : Index → Value, ∏ index, (laws index (values index)).toReal = 1 := by
  have mass : ∑ values : Index → Value, productPMF laws values = 1 :=
    (tsum_fintype _).symm.trans (PMF.tsum_coe _)
  calc ∑ values : Index → Value, ∏ index, (laws index (values index)).toReal
      = ∑ values : Index → Value, (productPMF laws values).toReal := by
        refine Finset.sum_congr rfl fun values _ => ?_
        rw [productPMF_apply, ENNReal.toReal_prod]
    _ = 1 := by
        rw [← ENNReal.toReal_sum fun values _ => PMF.apply_ne_top _ values, mass,
          ENNReal.toReal_one]

/-- A product over all coordinates splits off one coordinate. -/
theorem prod_split_place {Monoid : Type} [CommMonoid Monoid] (place : Index)
    (term : Index → Monoid) :
    ∏ index, term index = term place * ∏ index ∈ Finset.univ.erase place, term index :=
  (Finset.mul_prod_erase Finset.univ term (Finset.mem_univ place)).symm

/-- A product over the coordinates other than `place` is a product over the subtype. -/
theorem prod_erase_subtype {Monoid : Type} [CommMonoid Monoid] (place : Index)
    (term : Index → Monoid) :
    ∏ index ∈ Finset.univ.erase place, term index =
      ∏ index : { index : Index // index ≠ place }, term index.val :=
  Finset.prod_subtype (Finset.univ.erase place) (fun index => by simp) term

/-- A sum over the coordinates splits into the value at `place` and the other coordinates. -/
theorem sum_split_place {Monoid : Type} [AddCommMonoid Monoid] (place : Index)
    (term : Value → ({ index : Index // index ≠ place } → Value) → Monoid) :
    ∑ values : Index → Value, term (values place) (fun index => values index.val) =
      ∑ value : Value, ∑ rest : { index : Index // index ≠ place } → Value, term value rest := by
  have pairs : (∑ pair : Value × ({ index : Index // index ≠ place } → Value), term pair.1 pair.2) =
      ∑ value : Value, ∑ rest : { index : Index // index ≠ place } → Value, term value rest :=
    Fintype.sum_prod_type _
  rw [← pairs]
  exact Fintype.sum_equiv (Equiv.funSplitAt place Value)
    (fun values => term (values place) fun index => values index.val)
    (fun pair => term pair.1 pair.2) fun _ => rfl

/-- The uniform law of a function type is the product of the uniform coordinate laws. -/
theorem uniformOfFintype_pi [Nonempty Value] :
    PMF.uniformOfFintype (Index → Value) = productPMF fun _ : Index => PMF.uniformOfFintype Value :=
  by
  ext values
  rw [PMF.uniformOfFintype_apply, productPMF_apply]
  simp only [PMF.uniformOfFintype_apply]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

/-- A product of coordinate binds is the bind of the product laws. -/
theorem productPMF_bind {Source : Type} [Fintype Source] (laws : Index → PMF Source)
    (continuation : Index → Source → PMF Value) :
    ((productPMF laws).bind fun sources =>
        productPMF fun index => continuation index (sources index)) =
      productPMF fun index => (laws index).bind (continuation index) := by
  ext values
  rw [PMF.bind_apply, tsum_fintype, productPMF_apply]
  have factor : ∀ index : Index,
      ((laws index).bind (continuation index)) (values index) =
        ∑ source : Source, laws index source * continuation index source (values index) := by
    intro index
    rw [PMF.bind_apply, tsum_fintype]
  rw [Finset.prod_congr rfl fun index _ => factor index,
    Fintype.prod_sum fun (index : Index) (source : Source) =>
      laws index source * continuation index source (values index)]
  refine Finset.sum_congr rfl fun sources _ => ?_
  rw [Finset.prod_mul_distrib, productPMF_apply, productPMF_apply]

/-! ### Resampling one coordinate -/

/-- The mass of an updated coordinate: the other coordinates must already agree. -/
theorem map_update_apply [DecidableEq Value] (fresh : PMF Value) (values target : Index → Value)
    (place : Index) :
    (fresh.map fun value => Function.update values place value) target =
      if ∀ index, index ≠ place → values index = target index then fresh (target place) else 0 := by
  rw [PMF.map_apply, tsum_fintype]
  by_cases agree : ∀ index, index ≠ place → values index = target index
  · rw [if_pos agree, Finset.sum_eq_single (target place)]
    · refine if_pos (funext fun index => ?_).symm
      by_cases same : index = place
      · rw [same, Function.update_self]
      · rw [Function.update_of_ne same, agree index same]
    · intro value _ different
      refine if_neg fun equal => different ?_
      rw [equal, Function.update_self]
    · intro absent
      exact absurd (Finset.mem_univ _) absent
  · rw [if_neg agree]
    refine Finset.sum_eq_zero fun value _ => if_neg fun equal => agree ?_
    intro index different
    rw [equal, Function.update_of_ne different]

/-- A sum over the coordinates in which all but one are pinned. -/
theorem sum_pin {Monoid : Type} [AddCommMonoid Monoid] [DecidableEq Value] (place : Index)
    (target : Index → Value) (term : (Index → Value) → Monoid) :
    ∑ values : Index → Value,
        (if ∀ index, index ≠ place → values index = target index then term values else 0) =
      ∑ value : Value, term (Function.update target place value) := by
  rw [← Finset.sum_filter]
  have image : (Finset.univ.filter
      fun values : Index → Value => ∀ index, index ≠ place → values index = target index) =
      Finset.univ.image fun value : Value => Function.update target place value := by
    ext values
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro agree
      refine ⟨values place, funext fun index => ?_⟩
      by_cases same : index = place
      · rw [same, Function.update_self]
      · rw [Function.update_of_ne same, agree index same]
    · rintro ⟨value, rfl⟩ index different
      rw [Function.update_of_ne different]
  rw [image, Finset.sum_image]
  intro first _ second _ equal
  simpa using congrFun equal place

/-- Resampling one coordinate of a product law replaces that coordinate's law. -/
theorem productPMF_bind_update [DecidableEq Value] (laws : Index → PMF Value) (place : Index)
    (fresh : PMF Value) :
    ((productPMF laws).bind fun values =>
        fresh.map fun value => Function.update values place value) =
      productPMF (Function.update laws place fresh) := by
  ext target
  rw [PMF.bind_apply, tsum_fintype]
  simp only [map_update_apply, mul_ite, mul_zero]
  rw [sum_pin place target fun values => productPMF laws values * fresh (target place)]
  have pinned : ∀ value : Value,
      productPMF laws (Function.update target place value) =
        laws place value * ∏ index ∈ Finset.univ.erase place, laws index (target index) := by
    intro value
    rw [productPMF_apply, prod_split_place place, Function.update_self]
    refine congrArg (laws place value * ·) (Finset.prod_congr rfl fun index member => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase member)]
  simp only [pinned]
  rw [← Finset.sum_mul, ← Finset.sum_mul,
    show ∑ value : Value, laws place value = 1 from
      (tsum_fintype _).symm.trans (PMF.tsum_coe (laws place)),
    one_mul, productPMF_apply, prod_split_place place, Function.update_self, mul_comm]
  refine congrArg (fresh (target place) * ·) (Finset.prod_congr rfl fun index member => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase member)]

/-! ### Coordinates a continuation never reads -/

/-- Replacing one coordinate's law is invisible to a continuation that never reads that
coordinate. -/
theorem productPMF_bind_update_congr {Outcome : Type} [DecidableEq Value]
    (laws : Index → PMF Value) (place : Index) (first second : PMF Value)
    (continuation : (Index → Value) → PMF Outcome)
    (unread : ∀ (values : Index → Value) (value : Value),
      continuation (Function.update values place value) = continuation values) :
    (productPMF (Function.update laws place first)).bind continuation =
      (productPMF (Function.update laws place second)).bind continuation := by
  have expand : productPMF (Function.update laws place first) =
      (productPMF (Function.update laws place second)).bind fun values =>
        first.map fun value => Function.update values place value := by
    rw [productPMF_bind_update, Function.update_idem]
  calc (productPMF (Function.update laws place first)).bind continuation
      = ((productPMF (Function.update laws place second)).bind fun values =>
          first.map fun value => Function.update values place value).bind continuation := by
        rw [expand]
    _ = (productPMF (Function.update laws place second)).bind continuation := by
        rw [PMF.bind_bind]
        refine congrArg (PMF.bind _) (funext fun values => ?_)
        rw [PMF.bind_map]
        simp only [Function.comp_def, unread, PMF.bind_const]

/-- Two product laws that agree off a finite set of coordinates give the same game to a
continuation that never reads those coordinates. The digest replacement needs it because
the reference game's fiber sample is taken at the *selected* outputs, which differ from the
sampled hash secrets exactly at the gates whose input bit is set — and the fibers of those
gates are programmed nowhere. -/
theorem productPMF_bind_congr {Outcome : Type} [DecidableEq Value]
    (first second : Index → PMF Value) (changed : Finset Index)
    (continuation : (Index → Value) → PMF Outcome)
    (agree : ∀ index ∉ changed, first index = second index)
    (unread : ∀ index ∈ changed, ∀ (values : Index → Value) (value : Value),
      continuation (Function.update values index value) = continuation values) :
    (productPMF first).bind continuation = (productPMF second).bind continuation := by
  set mix : Finset Index → Index → PMF Value :=
    fun chosen index => if index ∈ chosen then first index else second index with mixDef
  have step : ∀ chosen : Finset Index, chosen ⊆ changed →
      (productPMF (mix chosen)).bind continuation =
        (productPMF second).bind continuation := by
    intro chosen
    induction chosen using Finset.induction with
    | empty =>
      intro _
      have same : mix ∅ = second := by
        funext index
        simp only [mixDef, Finset.notMem_empty, if_false]
      rw [same]
    | insert place chosen absent inductionHypothesis =>
      intro subset
      have placeMember : place ∈ changed := subset (Finset.mem_insert_self place chosen)
      have restSubset : chosen ⊆ changed := fun index member =>
        subset (Finset.mem_insert_of_mem member)
      have inserted : mix (insert place chosen) =
          Function.update (mix chosen) place (first place) := by
        funext index
        by_cases same : index = place
        · subst same
          simp only [mixDef, Finset.mem_insert, true_or, if_true, Function.update_self]
        · simp only [mixDef, Finset.mem_insert, same, false_or, Function.update_of_ne same]
      have unchanged : mix chosen = Function.update (mix chosen) place (second place) := by
        funext index
        by_cases same : index = place
        · subst same
          simp only [mixDef, if_neg absent, Function.update_self]
        · rw [Function.update_of_ne same]
      rw [inserted, productPMF_bind_update_congr (mix chosen) place (first place) (second place)
        continuation (unread place placeMember), ← unchanged]
      exact inductionHypothesis restSubset
  have full : mix changed = first := by
    funext index
    by_cases member : index ∈ changed
    · simp only [mixDef, if_pos member]
    · simp only [mixDef, if_neg member]
      exact (agree index member).symm
  have complete := step changed Finset.Subset.rfl
  rwa [full] at complete

/-! ### Coordinatewise subtypes -/

omit [DecidableEq Index] in
/-- The cast of a product of positive counts inverts factorwise. -/
theorem prod_natCast_inv (count : Index → Nat) (positive : ∀ index, count index ≠ 0) :
    ∏ index, ((count index : ENNReal))⁻¹ = ((∏ index, count index : Nat) : ENNReal)⁻¹ := by
  have cancel : (∏ index, ((count index : ENNReal))⁻¹) * ((∏ index, count index : Nat) : ENNReal) =
      1 := by
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun index _ => ?_
    exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (positive index))
      (ENNReal.natCast_ne_top _)
  have total : ((∏ index, count index : Nat) : ENNReal) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun index _ => positive index)
  calc ∏ index, ((count index : ENNReal))⁻¹
      = (∏ index, ((count index : ENNReal))⁻¹) *
          (((∏ index, count index : Nat) : ENNReal) * ((∏ index, count index : Nat) : ENNReal)⁻¹) := by
        rw [ENNReal.mul_inv_cancel total (ENNReal.natCast_ne_top _), mul_one]
    _ = ((∏ index, count index : Nat) : ENNReal)⁻¹ := by rw [← mul_assoc, cancel, one_mul]

/-- The uniform law of a coordinatewise subtype is the product of the uniform coordinate
subtype laws. -/
theorem uniform_subtypePi_map_val (predicate : Index → Value → Prop)
    [∀ index, DecidablePred (predicate index)]
    [∀ index, Nonempty { value : Value // predicate index value }]
    [Nonempty { values : Index → Value // ∀ index, predicate index (values index) }] :
    ((PMF.uniformOfFintype { values : Index → Value // ∀ index, predicate index (values index) }).map
        Subtype.val) =
      productPMF fun index =>
        (PMF.uniformOfFintype { value : Value // predicate index value }).map Subtype.val := by
  have counts : Fintype.card { values : Index → Value // ∀ index, predicate index (values index) } =
      ∏ index, Fintype.card { value : Value // predicate index value } := by
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi
      (p := fun index (value : Value) => predicate index value)), Fintype.card_pi]
  have coordinate : ∀ (index : Index) (value : Value),
      ((PMF.uniformOfFintype { value : Value // predicate index value }).map Subtype.val) value =
        if predicate index value then
          (Fintype.card { value : Value // predicate index value } : ENNReal)⁻¹ else 0 := by
    intro index value
    rw [PMF.map_apply, tsum_fintype]
    split
    · rename_i holds
      rw [Finset.sum_eq_single (⟨value, holds⟩ : { value : Value // predicate index value })]
      · rw [if_pos rfl, PMF.uniformOfFintype_apply]
      · intro element _ different
        exact if_neg fun equal => different (Subtype.ext equal.symm)
      · intro absent
        exact absurd (Finset.mem_univ _) absent
    · rename_i fails
      refine Finset.sum_eq_zero fun element _ => if_neg fun equal => fails ?_
      rw [equal]
      exact element.property
  ext values
  rw [productPMF_apply, PMF.map_apply, tsum_fintype]
  simp only [coordinate]
  by_cases holds : ∀ index, predicate index (values index)
  · rw [Finset.prod_congr rfl fun index _ => if_pos (holds index),
      prod_natCast_inv _ fun index => Fintype.card_ne_zero, ← counts,
      Finset.sum_eq_single (⟨values, holds⟩ :
        { values : Index → Value // ∀ index, predicate index (values index) })]
    · rw [if_pos rfl, PMF.uniformOfFintype_apply]
    · intro element _ different
      exact if_neg fun equal => different (Subtype.ext equal.symm)
    · intro absent
      exact absurd (Finset.mem_univ _) absent
  · obtain ⟨place, fails⟩ := not_forall.mp holds
    rw [Finset.prod_eq_zero (Finset.mem_univ place) (if_neg fails),
      Finset.sum_eq_zero fun element _ => if_neg fun equal => ?_]
    rw [equal] at fails
    exact fails (element.property place)

/-! ### Tensorisation of the total difference -/

/-- Replacing one coordinate law costs that coordinate's total difference. -/
theorem totalDifference_productPMF_update (laws : Index → PMF Value) (place : Index)
    (first second : PMF Value) :
    totalDifference (productPMF (Function.update laws place first))
        (productPMF (Function.update laws place second)) ≤ totalDifference first second := by
  have expand : ∀ (extra : PMF Value) (values : Index → Value),
      ((productPMF (Function.update laws place extra)) values).toReal =
        (extra (values place)).toReal *
          ∏ index : { index : Index // index ≠ place }, (laws index.val (values index.val)).toReal :=
    by
    intro extra values
    rw [productPMF_apply, ENNReal.toReal_prod, prod_split_place place, Function.update_self,
      ← prod_erase_subtype place fun index => (laws index (values index)).toReal]
    refine congrArg ((extra (values place)).toReal * ·) (Finset.prod_congr rfl
      fun index member => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase member)]
  unfold totalDifference
  simp only [expand, ← sub_mul, abs_mul]
  have rest : ∀ (value : Value) (values : { index : Index // index ≠ place } → Value),
      |∏ index : { index : Index // index ≠ place }, (laws index.val (values index)).toReal| =
        ∏ index : { index : Index // index ≠ place }, (laws index.val (values index)).toReal := by
    intro value values
    exact abs_of_nonneg (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
  refine le_of_eq ?_
  rw [Finset.sum_congr rfl fun values _ => congrArg
    (|(first (values place)).toReal - (second (values place)).toReal| * ·)
    (rest (values place) fun index => values index.val)]
  rw [sum_split_place place fun value values =>
    |(first value).toReal - (second value).toReal| *
      ∏ index : { index : Index // index ≠ place }, (laws index.val (values index)).toReal]
  refine Finset.sum_congr rfl fun value _ => ?_
  rw [← Finset.mul_sum, sum_toReal_productPMF fun index : { index : Index // index ≠ place } =>
    laws index.val, mul_one]

/-- The total difference of two products is at most the sum of the coordinate total
differences. -/
theorem totalDifference_productPMF (first second : Index → PMF Value) :
    totalDifference (productPMF first) (productPMF second) ≤
      ∑ index, totalDifference (first index) (second index) := by
  set mix : Finset Index → Index → PMF Value :=
    fun chosen index => if index ∈ chosen then first index else second index with mixDef
  have step : ∀ chosen : Finset Index,
      totalDifference (productPMF (mix chosen)) (productPMF second) ≤
        ∑ index ∈ chosen, totalDifference (first index) (second index) := by
    intro chosen
    induction chosen using Finset.induction with
    | empty =>
      have same : mix ∅ = second := by
        funext index
        simp only [mixDef, Finset.notMem_empty, if_false]
      rw [same, Finset.sum_empty]
      simp only [totalDifference, sub_self, abs_zero, Finset.sum_const_zero, le_refl]
    | insert place chosen absent inductionHypothesis =>
      have inserted : mix (insert place chosen) = Function.update (mix chosen) place (first place) :=
        by
        funext index
        by_cases same : index = place
        · subst same
          simp only [mixDef, Finset.mem_insert, true_or, if_true, Function.update_self]
        · simp only [mixDef, Finset.mem_insert, same, false_or, Function.update_of_ne same]
      have unchanged : mix chosen = Function.update (mix chosen) place (second place) := by
        funext index
        by_cases same : index = place
        · subst same
          simp only [mixDef, if_neg absent, Function.update_self]
        · rw [Function.update_of_ne same]
      calc totalDifference (productPMF (mix (insert place chosen))) (productPMF second)
          ≤ totalDifference (productPMF (mix (insert place chosen)))
              (productPMF (mix chosen)) +
            totalDifference (productPMF (mix chosen)) (productPMF second) :=
            totalDifference_triangle _ _ _
        _ ≤ totalDifference (first place) (second place) +
            ∑ index ∈ chosen, totalDifference (first index) (second index) := by
            refine add_le_add ?_ inductionHypothesis
            rw [inserted]
            nth_rewrite 2 [unchanged]
            exact totalDifference_productPMF_update (mix chosen) place (first place) (second place)
        _ = ∑ index ∈ insert place chosen, totalDifference (first index) (second index) :=
            (Finset.sum_insert (f := fun index => totalDifference (first index) (second index))
              absent).symm
  have full : mix Finset.univ = first := by
    funext index
    simp only [mixDef, Finset.mem_univ, if_true]
  have := step Finset.univ
  rwa [full] at this

end Product

end

end Kriterion.ArgoMAC.Security
