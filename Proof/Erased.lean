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

end

end Kriterion.ArgoMAC.Security
