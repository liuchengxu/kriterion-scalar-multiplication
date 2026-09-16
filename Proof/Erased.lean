/-
This file prices the one bad point of the steering hop that no label deferral
can reach: the image the reference game's programming erases.

The reference game's second stage runs on `programmed π ℓ s`, the unprogrammed
permutation `π` reprogrammed at the selected label `ℓ` of the steering gate to
the steered range `s`. The steered reference game's second stage runs on the
same permutation programmed twice, honestly and then steered. The two differ
exactly at the four points slice 3k identified, and three of them are
conditions on a hash-fiber chunk that one side never reads. The fourth is the
erased image `ρ = π ℓ`: a forward second-stage query is bad when its *answer*
is `ρ`, an inverse one when its *argument* is `ρ`.

The content here is that `ρ` is invisible. Conditionally on the first stage's
transcript -- an injective partial assignment that leaves `ℓ` unpinned and `s`
unused -- the pair (programmed view, erased image) is an exact product: the
view is uniform over the permutations compatible with the transcript re-pinned
at `ℓ` to `s`, and the erased image is uniform over the values the transcript
has not pinned, *independent of the view*. That is the `repin` bijection of
`Proof/Lazy.lean` read as a statement about laws. The second stage therefore
learns nothing about `ρ`, and a union bound over its log charges each entry
`1 / (2 ^ 128 - q)`.
-/

import Proof.Lazy
import Proof.Retarget

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-! ### The erased image is independent of the programmed view -/

/-- Reading a uniform compatible permutation through one programming splits into an
independent pair: the programmed view, uniform over the permutations compatible with the
transcript re-pinned at the label to the programmed range, and the erased image, uniform
over the values the transcript has not pinned.

This is the law-level reading of the `repin` bijection. Both hypotheses are the hop's own
good event: the first stage has not queried the selected label, and has not hit the steered
range. -/
theorem compatibleLaw_programmed {Result : Type} (assign : Assignment)
    (injective : AssignmentInjective assign) (label range : Block)
    (fresh : assign label = none) (unused : range ∉ pinnedRange assign)
    (continuation : Equiv Block Block → Block → PMF Result) :
    ((compatibleLaw assign).bind fun permutation =>
        continuation (programmed permutation label range) (permutation label)) =
      (freshValueLaw assign).bind fun erased =>
        (compatibleLaw (Function.update assign label (some range))).bind fun view =>
          continuation view erased := by
  classical
  haveI unusedNonempty : Nonempty {value : Block // value ∉ pinnedRange assign} :=
    ⟨⟨range, unused⟩⟩
  rw [compatibleLaw_forward assign injective label fresh
    (fun value permutation => continuation (programmed permutation label range) value)]
  refine bind_congr_support fun erased member => ?_
  have erasedFresh : erased ∉ pinnedRange assign :=
    freshValueLaw_support assign unusedNonempty member
  haveI leftNonempty :=
    nonempty_compatible _ (update_injective assign injective label erased erasedFresh)
  haveI rightNonempty :=
    nonempty_compatible _ (update_injective assign injective label range unused)
  rw [compatibleLaw_eq _ leftNonempty, compatibleLaw_eq _ rightNonempty,
    uniform_map_val_bind, uniform_map_val_bind,
    ← uniformOfFintype_bind_of_equiv (repin assign label erased range fresh erasedFresh unused)
      (fun view => continuation view.1 erased)]
  refine congrArg (PMF.bind _) (funext fun permutation => ?_)
  have pinned : permutation.1 label = erased :=
    permutation.2 label erased (by rw [Function.update_self])
  show continuation (programmed permutation.1 label range) erased = _
  rw [programmed, pinned]
  rfl

/-- The joint law of a run on the programmed view and the erased image factors: the run is
the run on a uniform view compatible with the re-pinned transcript, and the erased image is
an independent fresh value. -/
theorem erased_run_independent {Result : Type} {budget : Nat} (index : FixedKeyIndex)
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget)
    (state : State) (assign : Assignment) (injective : AssignmentInjective assign)
    (label range : Block) (fresh : assign label = none)
    (unused : range ∉ pinnedRange assign) :
    ((compatibleLaw assign).bind fun permutation =>
        (program.run idealOracle
            (setPermutation state index (programmed permutation label range))).map
          fun output => (output, permutation label)) =
      ((compatibleLaw (Function.update assign label (some range))).bind fun view =>
          program.run idealOracle (setPermutation state index view)).bind fun output =>
        (freshValueLaw assign).map fun erased => (output, erased) := by
  rw [compatibleLaw_programmed assign injective label range fresh unused
    (fun view erased => (program.run idealOracle (setPermutation state index view)).map
      fun output => (output, erased)),
    PMF.bind_bind]
  rw [PMF.bind_comm (freshValueLaw assign)
    (compatibleLaw (Function.update assign label (some range)))
    fun erased view => (program.run idealOracle (setPermutation state index view)).map
      fun output => (output, erased)]
  refine congrArg (PMF.bind _) (funext fun view => ?_)
  show ((freshValueLaw assign).bind fun erased =>
      (program.run idealOracle (setPermutation state index view)).bind fun output =>
        PMF.pure (output, erased)) =
    (program.run idealOracle (setPermutation state index view)).bind fun output =>
      (freshValueLaw assign).bind fun erased => PMF.pure (output, erased)
  exact PMF.bind_comm _ _ _

/-! ### The per-entry charge -/

/-- A fresh value takes any given value with probability at most `1 / (2 ^ 128 - budget)`. -/
theorem freshValueLaw_singleton_le (assign : Assignment) (injective : AssignmentInjective assign)
    (input : Block) (fresh : assign input = none) (budget : Nat)
    (small : pinnedCount assign ≤ budget) (value : Block) :
    (freshValueLaw assign).toOuterMeasure {value} ≤ (((2 ^ 128 - budget : Nat) : ENNReal))⁻¹ := by
  rw [← compatibleLaw_map_apply assign injective input fresh]
  exact compatibleLaw_singleton_le assign injective input fresh budget small value

/-- The erased image is never hit. A run on the programmed view produces a log; each entry
determines one candidate value (the answer of a forward query, the argument of an inverse
one), and the mass of "some entry's candidate is the erased image" is at most the log length
over `2 ^ 128 - budget`.

`point` is left arbitrary: it reads the whole outcome, so it may read the programmed view,
which is what a forward query's bad condition needs. -/
theorem erased_touch_le {Result : Type} {budget : Nat} (index : FixedKeyIndex)
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget)
    (state : State) (assign : Assignment) (injective : AssignmentInjective assign)
    (label range : Block) (fresh : assign label = none)
    (unused : range ∉ pinnedRange assign) (pinnedBound : Nat)
    (small : pinnedCount assign ≤ pinnedBound) (point : Result × State → Query → Block) :
    ((compatibleLaw assign).bind fun permutation =>
          (program.run idealOracle
              (setPermutation state index (programmed permutation label range))).map
            fun output => (output, permutation label)).toOuterMeasure
        {pair | ∃ entry ∈ pair.1.2.log, pair.2 = point pair.1 entry} ≤
      ((state.log.length + budget : Nat) : ENNReal) *
        (((2 ^ 128 - pinnedBound : Nat) : ENNReal))⁻¹ := by
  rw [erased_run_independent index program state assign injective label range fresh unused]
  refine Probability.bind_event_le _ _ _ _ fun output member => ?_
  rw [PMF.toOuterMeasure_map_apply]
  have entries : ((freshValueLaw assign).toOuterMeasure
      {erased | ∃ entry ∈ output.2.log, erased ∈ ({point output entry} : Set Block)}) ≤
      output.2.log.length * (((2 ^ 128 - pinnedBound : Nat) : ENNReal))⁻¹ :=
    toOuterMeasure_exists_mem_le_of_le (freshValueLaw assign) output.2.log
      (fun entry => {point output entry}) _
      fun entry _ => freshValueLaw_singleton_le assign injective label fresh pinnedBound small
        (point output entry)
  refine le_trans (le_trans (le_of_eq ?_) entries) ?_
  · rfl
  refine mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl
  obtain ⟨view, viewMember, runMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  have bound := run_idealOracle_log_length program (setPermutation state index view) output
    runMember
  rwa [setPermutation_log] at bound

/-! ### The four points at which the double programming differs -/

theorem programmed_apply (permutation : Equiv Block Block) (label range input : Block) :
    programmed permutation label range input =
      Equiv.swap (permutation label) range (permutation input) := rfl

theorem programmed_symm_apply (permutation : Equiv Block Block) (label range value : Block) :
    (programmed permutation label range).symm value =
      permutation.symm (Equiv.swap (permutation label) range value) := by
  rw [programmed, Equiv.symm_trans_apply, Equiv.symm_swap]

/-- Off the two forward points, programming a label twice answers a forward query as
programming it once to the second range. The two points are the preimages of the two
ranges. -/
theorem programmed_programmed_apply_of_ne (permutation : Equiv Block Block)
    (label honest steered input : Block) (notHonest : permutation input ≠ honest)
    (notSteered : permutation input ≠ steered) :
    programmed (programmed permutation label honest) label steered input =
      programmed permutation label steered input := by
  rw [programmed_apply (programmed permutation label honest), programmed_apply_label,
    programmed_apply, programmed_apply]
  by_cases same : permutation input = permutation label
  · rw [same, Equiv.swap_apply_left, Equiv.swap_apply_left, Equiv.swap_apply_left]
  · rw [Equiv.swap_apply_of_ne_of_ne same notHonest,
      Equiv.swap_apply_of_ne_of_ne same notSteered,
      Equiv.swap_apply_of_ne_of_ne notHonest notSteered]

/-- Off the two inverse points, programming a label twice answers an inverse query as
programming it once to the second range. The two points are the first range and the image
the programming erases. -/
theorem programmed_programmed_symm_apply_of_ne (permutation : Equiv Block Block)
    (label honest steered value : Block) (notHonest : value ≠ honest)
    (notErased : value ≠ permutation label) :
    (programmed (programmed permutation label honest) label steered).symm value =
      (programmed permutation label steered).symm value := by
  rw [programmed_symm_apply (programmed permutation label honest), programmed_apply_label,
    programmed_symm_apply, programmed_symm_apply]
  refine congrArg permutation.symm ?_
  by_cases same : value = steered
  · rw [same, Equiv.swap_apply_right honest steered,
      Equiv.swap_apply_right (permutation label) honest,
      Equiv.swap_apply_right (permutation label) steered]
  · rw [Equiv.swap_apply_of_ne_of_ne notHonest same,
      Equiv.swap_apply_of_ne_of_ne notErased notHonest,
      Equiv.swap_apply_of_ne_of_ne notErased same]

/-- The queries at which programming one index twice -- honestly and then steered -- differs
from programming it once to the steered range. A forward query is hidden when its image is
one of the two ranges; an inverse query when its argument is the honest range or the image
the programming erases. Queries at other indices and non-permutation queries hide nothing. -/
def steeringHidden (permutation : Equiv Block Block) (index : FixedKeyIndex)
    (label honest steered : Block) : Query → Prop
  | .fixedForward queryIndex input =>
      queryIndex = index ∧ (permutation input = honest ∨ permutation input = steered)
  | .fixedInverse queryIndex value =>
      queryIndex = index ∧ (value = honest ∨ value = permutation label)
  | _ => False

/-- Off its four hidden points, the doubly programmed view answers a query as the singly
programmed one. This is the identical-until-bad input of the steering hop. -/
theorem publicAnswer_steeringHidden (first second : View) (index : FixedKeyIndex)
    (permutation : Equiv Block Block) (label honest steered : Block)
    (sameRest : first.2 = second.2)
    (others : ∀ other, other ≠ index →
      first.1.permutation other = second.1.permutation other)
    (doubled : first.1.permutation index =
      programmed (programmed permutation label honest) label steered)
    (single : second.1.permutation index = programmed permutation label steered)
    (query : Query)
    (good : ¬ steeringHidden permutation index label honest steered query) :
    publicAnswer first query = publicAnswer second query := by
  cases query with
  | fixedForward queryIndex input =>
    show first.1.permutation queryIndex input = second.1.permutation queryIndex input
    by_cases same : queryIndex = index
    · subst same
      simp only [steeringHidden, true_and, not_or] at good
      rw [doubled, single]
      exact programmed_programmed_apply_of_ne permutation label honest steered input good.1
        good.2
    · rw [others queryIndex same]
  | fixedInverse queryIndex value =>
    show (first.1.permutation queryIndex).symm value =
      (second.1.permutation queryIndex).symm value
    by_cases same : queryIndex = index
    · subst same
      simp only [steeringHidden, true_and, not_or] at good
      rw [doubled, single]
      exact programmed_programmed_symm_apply_of_ne permutation label honest steered value
        good.1 good.2
    · rw [others queryIndex same]
  | encForward queryIndex value =>
    exact congrArg (fun rest : PermutationOracle Garbling.EncIndex Block ×
      (BaseField → Block × Block) => rest.1.permutation queryIndex value) sameRest
  | encInverse queryIndex value =>
    exact congrArg (fun rest : PermutationOracle Garbling.EncIndex Block ×
      (BaseField → Block × Block) => (rest.1.permutation queryIndex).symm value) sameRest
  | hash value =>
    exact congrArg (fun rest : PermutationOracle Garbling.EncIndex Block ×
      (BaseField → Block × Block) => randomOracleAnswer rest.2 value) sameRest

/-! ### The union bound over a log, keyed to each entry's own index -/

/-- A union bound over a finite family of tracked indices whose per-entry bad sets are empty
off the entry's own index.

The steering gate is programmed at three fixed-key indices (its hash slots) or at two (its
pad slots), and the conditional-uniformity tool tracks one index at a time. A permutation
query names exactly one index, so its bad set at the other tracked indices is empty; summing
the per-index bounds therefore costs one charge per *log entry*, not one per index. Charging
per index instead would cost three times as much and would not fit the hop's share of the
budget. -/
theorem toOuterMeasure_exists_mem_keyed_le {Sample Entry Index : Type} [DecidableEq Index]
    (law : PMF Sample) (indices : Finset Index) (entries : List Entry)
    (key : Entry → Option Index) (bad : Index → Entry → Set Sample) (charge : ENNReal)
    (each : ∀ index ∈ indices, ∀ entry ∈ entries, key entry = some index →
      law.toOuterMeasure (bad index entry) ≤ charge)
    (off : ∀ index ∈ indices, ∀ entry ∈ entries, key entry ≠ some index →
      bad index entry = ∅) :
    law.toOuterMeasure
        {sample | ∃ index ∈ indices, ∃ entry ∈ entries, sample ∈ bad index entry} ≤
      entries.length * charge := by
  induction entries with
  | nil =>
    have empty : {sample | ∃ index ∈ indices, ∃ entry ∈ ([] : List Entry),
        sample ∈ bad index entry} = (∅ : Set Sample) := by
      ext sample
      simp
    rw [empty, List.length_nil, Nat.cast_zero, zero_mul]
    exact le_of_eq (MeasureTheory.measure_empty (μ := law.toOuterMeasure))
  | cons entry rest inductionHypothesis =>
    have split : {sample | ∃ index ∈ indices, ∃ entry' ∈ entry :: rest,
          sample ∈ bad index entry'} =
        (⋃ index ∈ indices, bad index entry) ∪
          {sample | ∃ index ∈ indices, ∃ entry' ∈ rest, sample ∈ bad index entry'} := by
      ext sample
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro ⟨index, member, entry', head | tail, hit⟩
        · exact Or.inl ⟨index, member, head ▸ hit⟩
        · exact Or.inr ⟨index, member, entry', tail, hit⟩
      · rintro (⟨index, member, hit⟩ | ⟨index, member, entry', tail, hit⟩)
        · exact ⟨index, member, entry, Or.inl rfl, hit⟩
        · exact ⟨index, member, entry', Or.inr tail, hit⟩
    have head : law.toOuterMeasure (⋃ index ∈ indices, bad index entry) ≤ charge := by
      refine le_trans (MeasureTheory.measure_biUnion_finset_le indices _) ?_
      have pointwise : ∀ index ∈ indices,
          law.toOuterMeasure (bad index entry) ≤
            (if key entry = some index then charge else 0) := by
        intro index member
        by_cases keyed : key entry = some index
        · rw [if_pos keyed]
          exact each index member entry List.mem_cons_self keyed
        · rw [if_neg keyed, off index member entry List.mem_cons_self keyed]
          exact le_of_eq (MeasureTheory.measure_empty (μ := law.toOuterMeasure))
      refine le_trans (Finset.sum_le_sum pointwise) ?_
      cases key entry with
      | none => simp
      | some target =>
        simp only [Option.some_inj, Finset.sum_ite_eq]
        split
        · exact le_rfl
        · exact zero_le
    rw [split, List.length_cons, Nat.cast_succ, add_mul, one_mul,
      add_comm ((rest.length : ENNReal) * charge) charge]
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    exact add_le_add head (inductionHypothesis
      (fun index member entry' tail => each index member entry' (List.mem_cons_of_mem _ tail))
      (fun index member entry' tail => off index member entry' (List.mem_cons_of_mem _ tail)))

/-! ### The empty transcript, and one index of a uniform family -/

/-- The transcript a run starts from pins nothing. -/
theorem emptyAssignment_injective : AssignmentInjective (fun _ => none) := by
  intro _ _ _ pin
  exact absurd pin (by simp)

theorem pinnedCount_empty : pinnedCount (fun _ : Block => none) = 0 := by
  have empty : pinnedDomain (fun _ : Block => none) = (∅ : Set Block) := by
    ext input
    simp [pinnedDomain]
  rw [pinnedCount, empty, Set.ncard_empty]

/-- Before any query the conditional law of the tracked permutation is the uniform law.
This is the bridge from a game that samples the permutation family to `compatibleLaw_run`. -/
theorem compatibleLaw_empty :
    compatibleLaw (fun _ => none) = PMF.uniformOfFintype (Equiv Block Block) := by
  have holds : ∀ permutation : Equiv Block Block, Compatible (fun _ => none) permutation := by
    intro _ _ _ pin
    exact absurd pin (by simp)
  haveI nonempty : Nonempty {permutation : Equiv Block Block //
      Compatible (fun _ => none) permutation} := ⟨⟨Equiv.refl Block, holds _⟩⟩
  rw [compatibleLaw_eq _ nonempty]
  exact uniformOfFintype_map_bijection (Equiv.subtypeUnivEquiv holds)

/-- The permutation family with one index replaced. -/
def setOracleAt (oracle : PermutationOracle FixedKeyIndex Block) (index : FixedKeyIndex)
    (permutation : Equiv Block Block) : PermutationOracle FixedKeyIndex Block :=
  ⟨fun other => if other = index then permutation else oracle.permutation other⟩

theorem setPermutation_eq (state : State) (index : FixedKeyIndex)
    (permutation : Equiv Block Block) :
    setPermutation state index permutation =
      { state with view := (setOracleAt state.view.1 index permutation, state.view.2) } := rfl

theorem setOracleAt_permutation (oracle : PermutationOracle FixedKeyIndex Block)
    (index : FixedKeyIndex) (permutation : Equiv Block Block) :
    (setOracleAt oracle index permutation).permutation index = permutation := by
  show (if index = index then permutation else oracle.permutation index) = permutation
  rw [if_pos rfl]

theorem setOracleAt_self (oracle : PermutationOracle FixedKeyIndex Block)
    (index : FixedKeyIndex) : setOracleAt oracle index (oracle.permutation index) = oracle := by
  refine congrArg PermutationOracle.mk (funext fun other => ?_)
  show (if other = index then oracle.permutation index else oracle.permutation other) =
    oracle.permutation other
  by_cases same : other = index
  · rw [if_pos same, same]
  · rw [if_neg same]

/-- Exchanging one index of a permutation family with a separate sample is an involution. -/
def swapOracleAt (index : FixedKeyIndex) :
    PermutationOracle FixedKeyIndex Block × Equiv Block Block ≃
      PermutationOracle FixedKeyIndex Block × Equiv Block Block where
  toFun pair := (setOracleAt pair.1 index pair.2, pair.1.permutation index)
  invFun pair := (setOracleAt pair.1 index pair.2, pair.1.permutation index)
  left_inv pair := by
    obtain ⟨oracle, permutation⟩ := pair
    refine Prod.ext ?_ (setOracleAt_permutation oracle index permutation)
    show setOracleAt (setOracleAt oracle index permutation) index (oracle.permutation index) =
      oracle
    refine congrArg PermutationOracle.mk (funext fun other => ?_)
    show (if other = index then oracle.permutation index else
      (setOracleAt oracle index permutation).permutation other) = oracle.permutation other
    by_cases same : other = index
    · rw [if_pos same, same]
    · rw [if_neg same]
      show (if other = index then permutation else oracle.permutation other) =
        oracle.permutation other
      rw [if_neg same]
  right_inv pair := by
    obtain ⟨oracle, permutation⟩ := pair
    refine Prod.ext ?_ (setOracleAt_permutation oracle index permutation)
    show setOracleAt (setOracleAt oracle index permutation) index (oracle.permutation index) =
      oracle
    refine congrArg PermutationOracle.mk (funext fun other => ?_)
    show (if other = index then oracle.permutation index else
      (setOracleAt oracle index permutation).permutation other) = oracle.permutation other
    by_cases same : other = index
    · rw [if_pos same, same]
    · rw [if_neg same]
      show (if other = index then permutation else oracle.permutation other) =
        oracle.permutation other
      rw [if_neg same]

/-- A uniform permutation family with one index freshly resampled is a uniform permutation
family: the tracked index may be sampled after everything else. -/
theorem uniform_bind_setOracleAt {Outcome : Type} (index : FixedKeyIndex)
    (continuation : PermutationOracle FixedKeyIndex Block → PMF Outcome) :
    ((PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype (Equiv Block Block)).bind fun permutation =>
          continuation (setOracleAt oracle index permutation)) =
      (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind continuation := by
  rw [uniformOfFintype_bind_prod]
  have swapped := uniformOfFintype_bind_equiv (swapOracleAt index)
    fun pair : PermutationOracle FixedKeyIndex Block × Equiv Block Block => continuation pair.1
  simp only [swapOracleAt, Equiv.coe_fn_mk] at swapped
  have unprod : ((PMF.uniformOfFintype
        (PermutationOracle FixedKeyIndex Block × Equiv Block Block)).bind fun pair =>
      continuation pair.1) =
      (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype (Equiv Block Block)).bind fun _ => continuation oracle :=
    (uniformOfFintype_bind_prod
      fun oracle (_ : Equiv Block Block) => continuation oracle).symm
  rw [swapped, unprod]
  simp only [PMF.bind_const]

end

end Kriterion.ArgoMAC.Security
