/-
This file builds the lazy-sampling model of one fixed-key permutation.

A transcript pins finitely many inputs of the permutation to their images; that
partial injective assignment is the only thing an adversary has learned about the
permutation. The eager model samples the whole permutation before the run; the
lazy model carries the assignment and answers an unpinned query by a uniform
choice among the values the assignment leaves free. The two laws of
`(result, log, permutation)` agree, so conditionally on a transcript the
permutation is uniform over the compatible permutations, and its value at an
unpinned input is uniform over the unpinned values.

The counting core is the challenge library's `Cryptography/Permutation.lean`:
`programCompatiblePermutationEquiv` is the joint statement that programming a
fresh input of a compatible permutation is independent of the image that the
programming erases. Everything here is built on that one bijection.
-/

import Proof.Logged
import Proof.Uniform
import Cryptography.Permutation

namespace Kriterion.ArgoMAC.Security

open Cryptography

noncomputable section

/-! ### Partial assignments -/

/-- A transcript pins some inputs of one permutation to their images. -/
abbrev Assignment := Block → Option Block

/-- An assignment is injective when no two inputs are pinned to one value. -/
def AssignmentInjective (assign : Assignment) : Prop :=
  ∀ first second value, assign first = some value → assign second = some value → first = second

/-- A permutation is compatible with an assignment when it agrees at every pinned input. -/
def Compatible (assign : Assignment) (permutation : Equiv Block Block) : Prop :=
  ∀ input value, assign input = some value → permutation input = value

/-- The inputs an assignment pins. -/
def pinnedDomain (assign : Assignment) : Set Block := {input | (assign input).isSome}

/-- The values an assignment pins. -/
def pinnedRange (assign : Assignment) : Set Block := {value | ∃ input, assign input = some value}

theorem mem_pinnedDomain {assign : Assignment} {input value : Block}
    (pinned : assign input = some value) : input ∈ pinnedDomain assign := by
  simp only [pinnedDomain, Set.mem_ofPred_eq, pinned, Option.isSome_some]

theorem mem_pinnedRange {assign : Assignment} {input value : Block}
    (pinned : assign input = some value) : value ∈ pinnedRange assign := ⟨input, pinned⟩

theorem notMem_pinnedDomain {assign : Assignment} {input : Block}
    (fresh : assign input = none) : input ∉ pinnedDomain assign := by
  simp only [pinnedDomain, Set.mem_ofPred_eq, fresh, Option.isSome_none, Bool.false_eq_true,
    not_false_eq_true]

theorem eq_none_of_notMem_pinnedDomain {assign : Assignment} {input : Block}
    (fresh : input ∉ pinnedDomain assign) : assign input = none := by
  simp only [pinnedDomain, Set.mem_ofPred_eq, Option.isSome_iff_exists, not_exists] at fresh
  cases pinned : assign input with
  | none => rfl
  | some value => exact absurd pinned (fresh value)

/-- The pinned value of a pinned input. -/
def pinnedValue (assign : Assignment) (input : pinnedDomain assign) : pinnedRange assign :=
  ⟨(assign input.1).get input.2, ⟨input.1, (Option.some_get input.2).symm⟩⟩

theorem pinnedValue_spec (assign : Assignment) (input : pinnedDomain assign) :
    assign input.1 = some (pinnedValue assign input).1 :=
  (Option.some_get input.2).symm

/-- An injective assignment matches its pinned inputs with its pinned values. -/
def pinnedEquiv (assign : Assignment) (injective : AssignmentInjective assign) :
    pinnedDomain assign ≃ pinnedRange assign :=
  Equiv.ofBijective (pinnedValue assign) (by
    constructor
    · intro first second same
      have firstSpec := pinnedValue_spec assign first
      have secondSpec := pinnedValue_spec assign second
      rw [same] at firstSpec
      exact Subtype.ext (injective first.1 second.1 _ firstSpec secondSpec)
    · rintro ⟨value, input, pinned⟩
      refine ⟨⟨input, mem_pinnedDomain pinned⟩, Subtype.ext ?_⟩
      have spec := pinnedValue_spec assign ⟨input, mem_pinnedDomain pinned⟩
      rw [pinned] at spec
      exact (Option.some.inj spec).symm)

/-- Compatibility is the challenge library's assignment condition. -/
theorem compatible_iff (assign : Assignment) (injective : AssignmentInjective assign)
    (permutation : Equiv Block Block) :
    Compatible assign permutation ↔
      ∀ input : pinnedDomain assign,
        permutation input.1 = (pinnedEquiv assign injective input).1 := by
  constructor
  · intro compatible input
    exact compatible input.1 _ (pinnedValue_spec assign input)
  · intro agree input value pinned
    have spec := agree ⟨input, mem_pinnedDomain pinned⟩
    have value_eq := pinnedValue_spec assign ⟨input, mem_pinnedDomain pinned⟩
    rw [pinned] at value_eq
    rw [spec]
    exact (Option.some.inj value_eq).symm

noncomputable instance instFintypeCompatible (assign : Assignment) :
    Fintype {permutation : Equiv Block Block // Compatible assign permutation} :=
  Fintype.ofFinite _

noncomputable instance instFintypeUnused (assign : Assignment) :
    Fintype {value : Block // value ∉ pinnedRange assign} :=
  Fintype.ofFinite _

noncomputable instance instFintypeUnpinned (assign : Assignment) :
    Fintype {input : Block // assign input = none} :=
  Fintype.ofFinite _

noncomputable instance instFintypePinnedDomain (assign : Assignment) :
    Fintype (pinnedDomain assign) :=
  Fintype.ofFinite _

noncomputable instance instFintypePinnedRange (assign : Assignment) :
    Fintype (pinnedRange assign) :=
  Fintype.ofFinite _

noncomputable instance instFintypeOffDomain (assign : Assignment) :
    Fintype {input : Block // input ∉ pinnedDomain assign} :=
  Fintype.ofFinite _

/-- Every injective assignment is realised by some permutation. -/
theorem nonempty_compatible (assign : Assignment) (injective : AssignmentInjective assign) :
    Nonempty {permutation : Equiv Block Block // Compatible assign permutation} := by
  classical
  refine ⟨⟨(pinnedEquiv assign injective).extendSubtype, ?_⟩⟩
  refine (compatible_iff assign injective _).mpr fun input => ?_
  exact (pinnedEquiv assign injective).extendSubtype_apply_of_mem input.1 input.2

/-- An injective assignment pins as many values as inputs. -/
theorem card_pinnedRange (assign : Assignment) (injective : AssignmentInjective assign) :
    Fintype.card (pinnedRange assign) = Fintype.card (pinnedDomain assign) :=
  (Fintype.card_congr (pinnedEquiv assign injective)).symm

/-- An assignment that leaves one input free leaves one value free. -/
theorem unused_nonempty (assign : Assignment) (injective : AssignmentInjective assign)
    (input : Block) (fresh : assign input = none) :
    Nonempty {value : Block // value ∉ pinnedRange assign} := by
  have smaller : Fintype.card (pinnedDomain assign) < Fintype.card Block :=
    Fintype.card_subtype_lt (x := input) (notMem_pinnedDomain fresh)
  have count := card_pinnedRange assign injective
  have bridge : Fintype.card {value : Block // value ∈ pinnedRange assign} =
      Fintype.card (pinnedRange assign) := Fintype.card_congr (Equiv.refl _)
  have positive : 0 < Fintype.card {value : Block // value ∉ pinnedRange assign} := by
    rw [Fintype.card_subtype_compl (p := fun value => value ∈ pinnedRange assign)]
    omega
  exact Fintype.card_pos_iff.mp positive

/-- An assignment that leaves one value free leaves one input free. -/
theorem unpinned_nonempty (assign : Assignment) (injective : AssignmentInjective assign)
    (value : Block) (fresh : value ∉ pinnedRange assign) :
    Nonempty {input : Block // assign input = none} := by
  have smaller : Fintype.card (pinnedRange assign) < Fintype.card Block :=
    Fintype.card_subtype_lt (x := value) fresh
  have count := card_pinnedRange assign injective
  have bridge : Fintype.card {input : Block // input ∈ pinnedDomain assign} =
      Fintype.card (pinnedDomain assign) := Fintype.card_congr (Equiv.refl _)
  have positive : 0 < Fintype.card {input : Block // input ∉ pinnedDomain assign} := by
    rw [Fintype.card_subtype_compl (p := fun input => input ∈ pinnedDomain assign)]
    omega
  obtain ⟨witness⟩ := Fintype.card_pos_iff.mp positive
  exact ⟨⟨witness.1, eq_none_of_notMem_pinnedDomain witness.2⟩⟩

/-! ### Extending an assignment -/

/-- Compatibility with an extended assignment splits off the new pin. -/
theorem compatible_update_iff (assign : Assignment) (input value : Block)
    (fresh : assign input = none) (permutation : Equiv Block Block) :
    Compatible (Function.update assign input (some value)) permutation ↔
      Compatible assign permutation ∧ permutation input = value := by
  constructor
  · intro compatible
    refine ⟨fun other otherValue pinned => ?_, compatible input value (by simp)⟩
    have different : other ≠ input := by
      intro same
      rw [same, fresh] at pinned
      exact absurd pinned (by simp)
    exact compatible other otherValue (by rwa [Function.update_of_ne different])
  · rintro ⟨compatible, pinned⟩ other otherValue updated
    by_cases same : other = input
    · subst same
      rw [Function.update_self] at updated
      rw [pinned]
      exact Option.some.inj updated
    · rw [Function.update_of_ne same] at updated
      exact compatible other otherValue updated

/-- Pinning a free input to a free value keeps the assignment injective. -/
theorem update_injective (assign : Assignment) (injective : AssignmentInjective assign)
    (input value : Block) (freshValue : value ∉ pinnedRange assign) :
    AssignmentInjective (Function.update assign input (some value)) := by
  intro first second point firstPin secondPin
  by_cases firstSame : first = input <;> by_cases secondSame : second = input
  · rw [firstSame, secondSame]
  · subst firstSame
    rw [Function.update_self] at firstPin
    rw [Function.update_of_ne secondSame] at secondPin
    rw [Option.some.inj firstPin] at freshValue
    exact absurd (mem_pinnedRange secondPin) freshValue
  · subst secondSame
    rw [Function.update_self] at secondPin
    rw [Function.update_of_ne firstSame] at firstPin
    rw [Option.some.inj secondPin] at freshValue
    exact absurd (mem_pinnedRange firstPin) freshValue
  · rw [Function.update_of_ne firstSame] at firstPin
    rw [Function.update_of_ne secondSame] at secondPin
    exact injective first second point firstPin secondPin

/-! ### The three laws of the lazy model -/

open Classical in
/-- The law of the permutation given a transcript: uniform over the compatible permutations.
The fallback branch is unreachable for an injective assignment. -/
def compatibleLaw (assign : Assignment) : PMF (Equiv Block Block) :=
  if nonempty : Nonempty {permutation : Equiv Block Block // Compatible assign permutation} then
    (PMF.uniformOfFintype {permutation : Equiv Block Block // Compatible assign permutation}).map
      Subtype.val
  else PMF.pure (Equiv.refl Block)

open Classical in
/-- The law of a fresh forward answer: uniform over the values the transcript has not pinned. -/
def freshValueLaw (assign : Assignment) : PMF Block :=
  if nonempty : Nonempty {value : Block // value ∉ pinnedRange assign} then
    (PMF.uniformOfFintype {value : Block // value ∉ pinnedRange assign}).map Subtype.val
  else PMF.pure 0

open Classical in
/-- The law of a fresh inverse answer: uniform over the inputs the transcript has not pinned. -/
def freshInputLaw (assign : Assignment) : PMF Block :=
  if nonempty : Nonempty {input : Block // assign input = none} then
    (PMF.uniformOfFintype {input : Block // assign input = none}).map Subtype.val
  else PMF.pure 0

theorem compatibleLaw_eq (assign : Assignment)
    (nonempty : Nonempty {permutation : Equiv Block Block // Compatible assign permutation}) :
    compatibleLaw assign =
      (PMF.uniformOfFintype {permutation : Equiv Block Block //
        Compatible assign permutation}).map Subtype.val := by
  rw [compatibleLaw, dif_pos nonempty]

theorem freshValueLaw_eq (assign : Assignment)
    (nonempty : Nonempty {value : Block // value ∉ pinnedRange assign}) :
    freshValueLaw assign =
      (PMF.uniformOfFintype {value : Block // value ∉ pinnedRange assign}).map Subtype.val := by
  rw [freshValueLaw, dif_pos nonempty]

theorem freshInputLaw_eq (assign : Assignment)
    (nonempty : Nonempty {input : Block // assign input = none}) :
    freshInputLaw assign =
      (PMF.uniformOfFintype {input : Block // assign input = none}).map Subtype.val := by
  rw [freshInputLaw, dif_pos nonempty]

/-! ### Transporting a uniform sample along a bijection of finite types -/

/-- A uniform sample of one finite type is a uniform sample of any bijective copy. -/
theorem uniformOfFintype_bind_of_equiv {Value Other Result : Type} [Fintype Value] [Nonempty Value]
    [Fintype Other] [Nonempty Other] (bijection : Value ≃ Other)
    (continuation : Other → PMF Result) :
    ((PMF.uniformOfFintype Value).bind fun value => continuation (bijection value)) =
      (PMF.uniformOfFintype Other).bind continuation := by
  ext result
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  rw [Fintype.card_congr bijection]
  exact bijection.sum_comp fun value => (Fintype.card Other : ENNReal)⁻¹ * continuation value result

/-- A uniform sample mapped out of a subtype is a bind over the subtype. -/
theorem uniform_map_val_bind {Value Result : Type} {predicate : Value → Prop}
    [Fintype {value // predicate value}] [Nonempty {value // predicate value}]
    (continuation : Value → PMF Result) :
    (((PMF.uniformOfFintype {value // predicate value}).map Subtype.val).bind continuation) =
      (PMF.uniformOfFintype {value // predicate value}).bind fun value => continuation value.1 := by
  rw [PMF.map, PMF.bind_bind]
  exact congrArg (PMF.bind _) (funext fun value => PMF.pure_bind _ _)

/-! ### The fresh-point split -/

/-- Moving the new pin of an extended assignment from one free value to another. -/
def repin (assign : Assignment) (input first second : Block) (fresh : assign input = none)
    (firstFresh : first ∉ pinnedRange assign) (secondFresh : second ∉ pinnedRange assign) :
    {permutation : Equiv Block Block //
        Compatible (Function.update assign input (some first)) permutation} ≃
      {permutation : Equiv Block Block //
        Compatible (Function.update assign input (some second)) permutation} where
  toFun permutation := ⟨permutation.1.trans (Equiv.swap first second), by
    obtain ⟨compatible, pinned⟩ :=
      (compatible_update_iff assign input first fresh _).mp permutation.2
    refine (compatible_update_iff assign input second fresh _).mpr ⟨fun other value pin => ?_, ?_⟩
    · simp only [Equiv.trans_apply, compatible other value pin]
      exact Equiv.swap_apply_of_ne_of_ne (fun same => firstFresh (mem_pinnedRange (same ▸ pin)))
        (fun same => secondFresh (mem_pinnedRange (same ▸ pin)))
    · simp only [Equiv.trans_apply, pinned, Equiv.swap_apply_left]⟩
  invFun permutation := ⟨permutation.1.trans (Equiv.swap second first), by
    obtain ⟨compatible, pinned⟩ :=
      (compatible_update_iff assign input second fresh _).mp permutation.2
    refine (compatible_update_iff assign input first fresh _).mpr ⟨fun other value pin => ?_, ?_⟩
    · simp only [Equiv.trans_apply, compatible other value pin]
      exact Equiv.swap_apply_of_ne_of_ne (fun same => secondFresh (mem_pinnedRange (same ▸ pin)))
        (fun same => firstFresh (mem_pinnedRange (same ▸ pin)))
    · simp only [Equiv.trans_apply, pinned, Equiv.swap_apply_left]⟩
  left_inv permutation := by
    refine Subtype.ext (Equiv.ext fun point => ?_)
    simp only [Equiv.trans_apply]
    rw [Equiv.swap_comm second first, Equiv.swap_apply_self]
  right_inv permutation := by
    refine Subtype.ext (Equiv.ext fun point => ?_)
    simp only [Equiv.trans_apply]
    rw [Equiv.swap_comm first second, Equiv.swap_apply_self]

/-- Reprogramming a permutation at its own image is the identity. -/
theorem trans_swap_trans_swap (permutation : Equiv Block Block) (input value : Block) :
    (permutation.trans (Equiv.swap (permutation input) value)).trans
        (Equiv.swap value (permutation input)) = permutation := by
  refine Equiv.ext fun point => ?_
  simp only [Equiv.trans_apply]
  rw [Equiv.swap_comm value (permutation input), Equiv.swap_apply_self]

open Classical in
/-- The challenge library's fresh-point bijection in the language of assignments: a
compatible permutation is a permutation compatible with one chosen extra pin together
with the independent image that the extra pin erases. -/
def compatibleSplit (assign : Assignment) (injective : AssignmentInjective assign)
    (input : Block) (fresh : assign input = none)
    (base : Block) (baseFresh : base ∉ pinnedRange assign) :
    {permutation : Equiv Block Block // Compatible assign permutation} ≃
      {permutation : Equiv Block Block //
          Compatible (Function.update assign input (some base)) permutation} ×
        {value : Block // value ∉ pinnedRange assign} :=
  (Equiv.subtypeEquivRight (compatible_iff assign injective)).trans
    ((programCompatiblePermutationEquiv (pinnedDomain assign) (pinnedRange assign)
        (pinnedEquiv assign injective) input (notMem_pinnedDomain fresh) base baseFresh).trans
      (Equiv.prodCongr
        (Equiv.subtypeEquivRight fun permutation =>
          (compatible_update_iff assign input base fresh permutation).trans
            (and_congr (compatible_iff assign injective permutation) Iff.rfl)).symm
        (Equiv.subtypeEquivRight fun value => Iff.rfl).symm))

theorem compatibleSplit_fst (assign : Assignment) (injective : AssignmentInjective assign)
    (input : Block) (fresh : assign input = none)
    (base : Block) (baseFresh : base ∉ pinnedRange assign)
    (permutation : {permutation : Equiv Block Block // Compatible assign permutation}) :
    (compatibleSplit assign injective input fresh base baseFresh permutation).1.1 =
      permutation.1.trans (Equiv.swap (permutation.1 input) base) := rfl

theorem compatibleSplit_snd (assign : Assignment) (injective : AssignmentInjective assign)
    (input : Block) (fresh : assign input = none)
    (base : Block) (baseFresh : base ∉ pinnedRange assign)
    (permutation : {permutation : Equiv Block Block // Compatible assign permutation}) :
    (compatibleSplit assign injective input fresh base baseFresh permutation).2.1 =
      permutation.1 input := rfl

/-! ### The forward marginalisation -/

/-- Reading a uniform compatible permutation at an unpinned input is the same as drawing the
answer uniformly from the unpinned values first and conditioning the permutation on it. -/
theorem compatibleLaw_forward {Result : Type} (assign : Assignment)
    (injective : AssignmentInjective assign) (input : Block) (fresh : assign input = none)
    (continuation : Block → Equiv Block Block → PMF Result) :
    ((compatibleLaw assign).bind fun permutation => continuation (permutation input) permutation) =
      (freshValueLaw assign).bind fun value =>
        (compatibleLaw (Function.update assign input (some value))).bind fun permutation =>
          continuation value permutation := by
  classical
  obtain ⟨base⟩ := unused_nonempty assign injective input fresh
  haveI unusedNonempty : Nonempty {value : Block // value ∉ pinnedRange assign} := ⟨base⟩
  haveI compatibleNonempty := nonempty_compatible assign injective
  haveI baseNonempty : Nonempty {permutation : Equiv Block Block //
      Compatible (Function.update assign input (some base.1)) permutation} :=
    nonempty_compatible _ (update_injective assign injective input base.1 base.2)
  rw [compatibleLaw_eq assign compatibleNonempty, freshValueLaw_eq assign unusedNonempty,
    uniform_map_val_bind, uniform_map_val_bind]
  haveI extendedNonempty : ∀ value : {value : Block // value ∉ pinnedRange assign},
      Nonempty {permutation : Equiv Block Block //
        Compatible (Function.update assign input (some value.1)) permutation} := fun value =>
    nonempty_compatible _ (update_injective assign injective input value.1 value.2)
  have extended : ((PMF.uniformOfFintype {value : Block // value ∉ pinnedRange assign}).bind
        fun value => (compatibleLaw (Function.update assign input (some value.1))).bind
          fun permutation => continuation value.1 permutation) =
      (PMF.uniformOfFintype {value : Block // value ∉ pinnedRange assign}).bind fun value =>
        (PMF.uniformOfFintype {permutation : Equiv Block Block //
            Compatible (Function.update assign input (some value.1)) permutation}).bind
          fun permutation => continuation value.1 permutation.1 := by
    refine congrArg (PMF.bind _) (funext fun value => ?_)
    rw [compatibleLaw_eq _ (extendedNonempty value), uniform_map_val_bind]
  rw [extended]
  have transported := uniformOfFintype_bind_of_equiv
    (compatibleSplit assign injective input fresh base.1 base.2)
    (fun pair => continuation pair.2.1 (pair.1.1.trans (Equiv.swap base.1 pair.2.1)))
  have split : ((PMF.uniformOfFintype {permutation : Equiv Block Block //
        Compatible assign permutation}).bind fun permutation =>
          continuation (permutation.1 input) permutation.1) =
      (PMF.uniformOfFintype ({permutation : Equiv Block Block //
            Compatible (Function.update assign input (some base.1)) permutation} ×
          {value : Block // value ∉ pinnedRange assign})).bind fun pair =>
        continuation pair.2.1 (pair.1.1.trans (Equiv.swap base.1 pair.2.1)) := by
    rw [← transported]
    refine congrArg (PMF.bind _) (funext fun permutation => ?_)
    rw [compatibleSplit_snd, compatibleSplit_fst, trans_swap_trans_swap]
  have product := uniformOfFintype_bind_prod
    (Left := {permutation : Equiv Block Block //
      Compatible (Function.update assign input (some base.1)) permutation})
    (Right := {value : Block // value ∉ pinnedRange assign})
    (fun permutation value =>
      continuation value.1 (permutation.1.trans (Equiv.swap base.1 value.1)))
  rw [split, ← product, PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun value => ?_)
  exact uniformOfFintype_bind_of_equiv (repin assign input base.1 value.1 fresh base.2 value.2)
    (fun permutation => continuation value.1 permutation.1)

end

end Kriterion.ArgoMAC.Security
