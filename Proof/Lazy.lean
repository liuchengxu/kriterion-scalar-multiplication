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

import Proof.Chunk
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

/-- A mapped law continued is the law continued after the map. -/
theorem bind_of_map {Value Other Result : Type} (law : PMF Value) (step : Value → Other)
    (continuation : Other → PMF Result) :
    (law.map step).bind continuation = law.bind fun value => continuation (step value) := by
  rw [PMF.map, PMF.bind_bind]
  exact congrArg (PMF.bind _) (funext fun value => PMF.pure_bind _ _)

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

/-! ### The transposed assignment -/

open Classical in
/-- The input a transcript pins to a value. -/
def pinnedInput (assign : Assignment) (value : Block) : Option Block :=
  if pinned : ∃ input, assign input = some value then some pinned.choose else none

theorem pinnedInput_eq_some_iff (assign : Assignment) (injective : AssignmentInjective assign)
    (value input : Block) : pinnedInput assign value = some input ↔ assign input = some value := by
  classical
  constructor
  · intro transposed
    by_cases pinned : ∃ other, assign other = some value
    · rw [pinnedInput, dif_pos pinned] at transposed
      rw [← Option.some.inj transposed]
      exact pinned.choose_spec
    · rw [pinnedInput, dif_neg pinned] at transposed
      exact absurd transposed (by simp)
  · intro pin
    have pinned : ∃ other, assign other = some value := ⟨input, pin⟩
    rw [pinnedInput, dif_pos pinned]
    exact congrArg some (injective pinned.choose input value pinned.choose_spec pin)

theorem pinnedInput_eq_none (assign : Assignment) (injective : AssignmentInjective assign)
    (value : Block) (fresh : value ∉ pinnedRange assign) : pinnedInput assign value = none := by
  cases transposed : pinnedInput assign value with
  | none => rfl
  | some input =>
    exact absurd (mem_pinnedRange ((pinnedInput_eq_some_iff assign injective value input).mp
      transposed)) fresh

theorem pinnedInput_injective (assign : Assignment) (injective : AssignmentInjective assign) :
    AssignmentInjective (pinnedInput assign) := by
  intro first second input firstPin secondPin
  exact Option.some.inj
    (((pinnedInput_eq_some_iff assign injective first input).mp firstPin).symm.trans
      ((pinnedInput_eq_some_iff assign injective second input).mp secondPin))

theorem notMem_pinnedRange_pinnedInput (assign : Assignment)
    (injective : AssignmentInjective assign) (input : Block) :
    input ∉ pinnedRange (pinnedInput assign) ↔ assign input = none := by
  constructor
  · intro fresh
    cases pin : assign input with
    | none => rfl
    | some value =>
      exact absurd ⟨value, (pinnedInput_eq_some_iff assign injective value input).mpr pin⟩ fresh
  · rintro fresh ⟨value, transposed⟩
    rw [(pinnedInput_eq_some_iff assign injective value input).mp transposed] at fresh
    exact absurd fresh (by simp)

/-- A permutation is compatible with the transposed assignment exactly when its inverse
is compatible with the assignment. -/
theorem compatible_pinnedInput_iff (assign : Assignment) (injective : AssignmentInjective assign)
    (permutation : Equiv Block Block) :
    Compatible (pinnedInput assign) permutation ↔ Compatible assign permutation.symm := by
  constructor
  · intro compatible input value pin
    have transposed := (pinnedInput_eq_some_iff assign injective value input).mpr pin
    rw [← compatible value input transposed]
    exact permutation.symm_apply_apply value
  · intro compatible value input transposed
    have pin := (pinnedInput_eq_some_iff assign injective value input).mp transposed
    rw [← compatible input value pin]
    exact permutation.apply_symm_apply input

/-- Inverting a permutation matches the two compatibility conditions. -/
def compatibleSymm (assign : Assignment) (injective : AssignmentInjective assign) :
    {permutation : Equiv Block Block // Compatible (pinnedInput assign) permutation} ≃
      {permutation : Equiv Block Block // Compatible assign permutation} where
  toFun permutation :=
    ⟨permutation.1.symm, (compatible_pinnedInput_iff assign injective permutation.1).mp
      permutation.2⟩
  invFun permutation :=
    ⟨permutation.1.symm, (compatible_pinnedInput_iff assign injective permutation.1.symm).mpr
      (by rw [Equiv.symm_symm]; exact permutation.2)⟩
  left_inv permutation := Subtype.ext (Equiv.symm_symm permutation.1)
  right_inv permutation := Subtype.ext (Equiv.symm_symm permutation.1)

/-- A uniform choice out of two equal subtypes is the same law. -/
theorem uniform_map_val_congr {Value : Type} {predicate otherPredicate : Value → Prop}
    [Fintype {value // predicate value}] [Nonempty {value // predicate value}]
    [Fintype {value // otherPredicate value}] [Nonempty {value // otherPredicate value}]
    (same : ∀ value, predicate value ↔ otherPredicate value) :
    (PMF.uniformOfFintype {value // predicate value}).map Subtype.val =
      (PMF.uniformOfFintype {value // otherPredicate value}).map Subtype.val := by
  have transported := uniformOfFintype_bind_of_equiv (Equiv.subtypeEquivRight same)
    (fun value => PMF.pure value.1)
  rw [PMF.map, PMF.map, Function.comp_def, Function.comp_def]
  exact transported

/-- Reading a compatible permutation is reading the inverse of a transposed one. -/
theorem compatibleLaw_bind_symm {Result : Type} (assign : Assignment)
    (injective : AssignmentInjective assign) (continuation : Equiv Block Block → PMF Result) :
    (compatibleLaw assign).bind continuation =
      (compatibleLaw (pinnedInput assign)).bind fun permutation =>
        continuation permutation.symm := by
  haveI forwardNonempty := nonempty_compatible assign injective
  haveI inverseNonempty :=
    nonempty_compatible (pinnedInput assign) (pinnedInput_injective assign injective)
  rw [compatibleLaw_eq assign forwardNonempty,
    compatibleLaw_eq (pinnedInput assign) inverseNonempty, uniform_map_val_bind,
    uniform_map_val_bind]
  exact (uniformOfFintype_bind_of_equiv (compatibleSymm assign injective)
    (fun permutation => continuation permutation.1)).symm

/-- Pinning a free input to a free value transposes to pinning that value to that input. -/
theorem pinnedInput_update (assign : Assignment) (injective : AssignmentInjective assign)
    (input value : Block) (freshInput : assign input = none)
    (freshValue : value ∉ pinnedRange assign) :
    pinnedInput (Function.update assign input (some value)) =
      Function.update (pinnedInput assign) value (some input) := by
  have updated := update_injective assign injective input value freshValue
  funext other
  refine Option.ext fun point => ?_
  show pinnedInput (Function.update assign input (some value)) other = some point ↔
    Function.update (pinnedInput assign) value (some input) other = some point
  rw [pinnedInput_eq_some_iff _ updated]
  by_cases sameValue : other = value
  · subst sameValue
    rw [Function.update_self]
    constructor
    · intro pin
      by_cases samePoint : point = input
      · rw [samePoint]
      · rw [Function.update_of_ne samePoint] at pin
        exact absurd (mem_pinnedRange pin) freshValue
    · intro pin
      rw [Option.some.inj pin, Function.update_self]
  · rw [Function.update_of_ne sameValue, pinnedInput_eq_some_iff _ injective]
    by_cases samePoint : point = input
    · subst samePoint
      rw [Function.update_self, freshInput]
      constructor
      · intro pin
        exact absurd (Option.some.inj pin).symm sameValue
      · intro pin
        exact absurd pin (by simp)
    · rw [Function.update_of_ne samePoint]

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

/-! ### The inverse marginalisation -/

/-- The fresh inverse answers of an assignment are the fresh forward answers of its transpose. -/
theorem freshValueLaw_pinnedInput (assign : Assignment) (injective : AssignmentInjective assign)
    (nonempty : Nonempty {input : Block // assign input = none}) :
    freshValueLaw (pinnedInput assign) = freshInputLaw assign := by
  have witness := Classical.choice nonempty
  haveI transposedNonempty :
      Nonempty {value : Block // value ∉ pinnedRange (pinnedInput assign)} :=
    ⟨⟨witness.1, (notMem_pinnedRange_pinnedInput assign injective witness.1).mpr witness.2⟩⟩
  rw [freshValueLaw_eq _ transposedNonempty, freshInputLaw_eq assign nonempty]
  exact uniform_map_val_congr (notMem_pinnedRange_pinnedInput assign injective)

theorem freshInputLaw_support (assign : Assignment)
    (nonempty : Nonempty {input : Block // assign input = none}) {input : Block}
    (member : input ∈ (freshInputLaw assign).support) : assign input = none := by
  rw [freshInputLaw_eq assign nonempty, PMF.support_map] at member
  obtain ⟨witness, _, rfl⟩ := member
  exact witness.2

/-- Inverting a uniform compatible permutation at an unpinned value is the same as drawing the
preimage uniformly from the unpinned inputs first and conditioning the permutation on it. -/
theorem compatibleLaw_inverse {Result : Type} (assign : Assignment)
    (injective : AssignmentInjective assign) (value : Block) (fresh : value ∉ pinnedRange assign)
    (continuation : Block → Equiv Block Block → PMF Result) :
    ((compatibleLaw assign).bind fun permutation =>
        continuation (permutation.symm value) permutation) =
      (freshInputLaw assign).bind fun input =>
        (compatibleLaw (Function.update assign input (some value))).bind fun permutation =>
          continuation input permutation := by
  haveI unpinned := unpinned_nonempty assign injective value fresh
  have transposedInjective := pinnedInput_injective assign injective
  have step : ((compatibleLaw assign).bind fun permutation =>
        continuation (permutation.symm value) permutation) =
      (compatibleLaw (pinnedInput assign)).bind fun permutation =>
        continuation (permutation value) permutation.symm := by
    rw [compatibleLaw_bind_symm assign injective
      (fun permutation => continuation (permutation.symm value) permutation)]
    refine congrArg (PMF.bind _) (funext fun permutation => ?_)
    rw [Equiv.symm_symm]
  rw [step, compatibleLaw_forward (pinnedInput assign) transposedInjective value
      (pinnedInput_eq_none assign injective value fresh)
      (fun answer permutation => continuation answer permutation.symm),
    freshValueLaw_pinnedInput assign injective unpinned]
  refine bind_congr_support fun input member => ?_
  rw [← pinnedInput_update assign injective input value
    (freshInputLaw_support assign unpinned member) fresh]
  exact (compatibleLaw_bind_symm (Function.update assign input (some value))
    (update_injective assign injective input value fresh)
    (fun permutation => continuation input permutation)).symm

/-! ### Supports -/

theorem compatibleLaw_support (assign : Assignment) (injective : AssignmentInjective assign)
    {permutation : Equiv Block Block} (member : permutation ∈ (compatibleLaw assign).support) :
    Compatible assign permutation := by
  rw [compatibleLaw_eq assign (nonempty_compatible assign injective), PMF.support_map] at member
  obtain ⟨witness, _, rfl⟩ := member
  exact witness.2

theorem freshValueLaw_support (assign : Assignment)
    (nonempty : Nonempty {value : Block // value ∉ pinnedRange assign}) {value : Block}
    (member : value ∈ (freshValueLaw assign).support) : value ∉ pinnedRange assign := by
  rw [freshValueLaw_eq assign nonempty, PMF.support_map] at member
  obtain ⟨witness, _, rfl⟩ := member
  exact witness.2

theorem notMem_pinnedRange_of_pinnedInput_eq_none (assign : Assignment)
    (injective : AssignmentInjective assign) {value : Block}
    (transposed : pinnedInput assign value = none) : value ∉ pinnedRange assign := by
  rintro ⟨input, pin⟩
  rw [(pinnedInput_eq_some_iff assign injective value input).mpr pin] at transposed
  exact absurd transposed (by simp)

/-! ### The lazy handler -/

/-- Replace the fixed-key permutation at one index. -/
def setPermutation (state : State) (index : FixedKeyIndex) (permutation : Equiv Block Block) :
    State :=
  { state with view := (⟨fun other => if other = index then permutation else
      state.view.1.permutation other⟩, state.view.2) }

theorem setPermutation_log (state : State) (index : FixedKeyIndex)
    (permutation : Equiv Block Block) : (setPermutation state index permutation).log = state.log :=
  rfl

theorem setPermutation_logged (state : State) (index : FixedKeyIndex)
    (permutation : Equiv Block Block) (request : Query) :
    { setPermutation state index permutation with log := request :: state.log } =
      setPermutation { state with log := request :: state.log } index permutation := rfl

theorem publicAnswer_setPermutation_forward (state : State) (index : FixedKeyIndex)
    (permutation : Equiv Block Block) (domain : Block) :
    publicAnswer (setPermutation state index permutation).view
        (PublicQuery.fixedForward index domain) = permutation domain := by
  simp only [publicAnswer, setPermutation, if_pos]
  rfl

theorem publicAnswer_setPermutation_inverse (state : State) (index : FixedKeyIndex)
    (permutation : Equiv Block Block) (range : Block) :
    publicAnswer (setPermutation state index permutation).view
        (PublicQuery.fixedInverse index range) = permutation.symm range := by
  simp only [publicAnswer, setPermutation, if_pos]
  rfl

theorem publicAnswer_setPermutation_forward_of_ne (state : State) (index queryIndex : FixedKeyIndex)
    (permutation : Equiv Block Block) (domain : Block) (different : queryIndex ≠ index) :
    publicAnswer (setPermutation state index permutation).view
        (PublicQuery.fixedForward queryIndex domain) =
      publicAnswer state.view (PublicQuery.fixedForward queryIndex domain) := by
  simp only [publicAnswer, setPermutation, if_neg different]
  rfl

theorem publicAnswer_setPermutation_inverse_of_ne (state : State) (index queryIndex : FixedKeyIndex)
    (permutation : Equiv Block Block) (range : Block) (different : queryIndex ≠ index) :
    publicAnswer (setPermutation state index permutation).view
        (PublicQuery.fixedInverse queryIndex range) =
      publicAnswer state.view (PublicQuery.fixedInverse queryIndex range) := by
  simp only [publicAnswer, setPermutation, if_neg different]
  rfl

/-- The lazy handler answers a tracked fixed-key query from the assignment, extending it by a
uniform choice among the free values when the query is not yet pinned, and answers every other
query from the view. -/
def lazyAnswer (index : FixedKeyIndex) (view : View) :
    (request : Query) → Assignment → PMF (request.Answer × Assignment)
  | .fixedForward queryIndex domain, assign =>
      if queryIndex = index then
        (assign domain).elim
          ((freshValueLaw assign).map fun value =>
            (value, Function.update assign domain (some value)))
          (fun value => PMF.pure (value, assign))
      else PMF.pure (view.1.permutation queryIndex domain, assign)
  | .fixedInverse queryIndex range, assign =>
      if queryIndex = index then
        (pinnedInput assign range).elim
          ((freshInputLaw assign).map fun domain =>
            (domain, Function.update assign domain (some range)))
          (fun domain => PMF.pure (domain, assign))
      else PMF.pure ((view.1.permutation queryIndex).symm range, assign)
  | .encForward queryIndex domain, assign =>
      PMF.pure (view.2.1.permutation queryIndex domain, assign)
  | .encInverse queryIndex range, assign =>
      PMF.pure ((view.2.1.permutation queryIndex).symm range, assign)
  | .hash point, assign => PMF.pure (randomOracleAnswer view.2.2 point, assign)

/-- The lazy run: the tracked permutation is never sampled, only its transcript. -/
def lazyRun {Result : Type} (index : FixedKeyIndex) :
    {budget : Nat} →
      OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget →
        State → Assignment → PMF ((Result × List Query) × Assignment)
  | _, .pure distribution, state, assign =>
      distribution.map fun value => ((value, state.log), assign)
  | _, .query request next, state, assign =>
      (lazyAnswer index state.view request assign).bind fun pair =>
        lazyRun index (next pair.1) { state with log := request :: state.log } pair.2
  | _, .sample distribution next, state, assign =>
      distribution.bind fun value => lazyRun index (next value) state assign

/-! ### The eager-to-lazy equivalence -/

/-- One query step: the eager answer read off a uniform compatible permutation and the lazy
answer drawn from the assignment continue into the same law. -/
theorem lazy_query_step {Outcome : Type} (index : FixedKeyIndex) (request : Query)
    (state : State) (assign : Assignment) (injective : AssignmentInjective assign)
    (eager : (answer : request.Answer) → Equiv Block Block → PMF Outcome)
    (lazy : (answer : request.Answer) → Assignment → PMF Outcome)
    (step : ∀ (answer : request.Answer) (other : Assignment), AssignmentInjective other →
      ((compatibleLaw other).bind fun permutation => eager answer permutation) =
        lazy answer other) :
    ((compatibleLaw assign).bind fun permutation =>
        eager (publicAnswer (setPermutation state index permutation).view request) permutation) =
      (lazyAnswer index state.view request assign).bind fun pair => lazy pair.1 pair.2 := by
  cases request with
  | fixedForward queryIndex domain =>
    by_cases tracked : queryIndex = index
    · subst tracked
      cases pinned : assign domain with
      | some value =>
        have lazyEq : lazyAnswer queryIndex state.view
            (PublicQuery.fixedForward queryIndex domain) assign = PMF.pure (value, assign) := by
          simp [lazyAnswer, pinned]
          rfl
        calc ((compatibleLaw assign).bind fun permutation =>
              eager (publicAnswer (setPermutation state queryIndex permutation).view
                (PublicQuery.fixedForward queryIndex domain)) permutation)
            = (compatibleLaw assign).bind (fun permutation => eager value permutation) := by
              refine bind_congr_support fun permutation member => ?_
              rw [publicAnswer_setPermutation_forward,
                compatibleLaw_support assign injective member domain value pinned]
          _ = lazy value assign := step value assign injective
          _ = (lazyAnswer queryIndex state.view (PublicQuery.fixedForward queryIndex domain)
                assign).bind fun pair => lazy pair.1 pair.2 := by
              rw [lazyEq]
              exact (PMF.pure_bind (value, assign) fun pair => lazy pair.1 pair.2).symm
      | none =>
        have lazyEq : lazyAnswer queryIndex state.view
            (PublicQuery.fixedForward queryIndex domain) assign =
            (freshValueLaw assign).map fun value =>
              (value, Function.update assign domain (some value)) := by
          simp [lazyAnswer, pinned]
          rfl
        calc ((compatibleLaw assign).bind fun permutation =>
              eager (publicAnswer (setPermutation state queryIndex permutation).view
                (PublicQuery.fixedForward queryIndex domain)) permutation)
            = (compatibleLaw assign).bind (fun permutation =>
                eager (permutation domain) permutation) := by
              refine congrArg (PMF.bind _) (funext fun permutation => ?_)
              rw [publicAnswer_setPermutation_forward]
          _ = (freshValueLaw assign).bind (fun value =>
                (compatibleLaw (Function.update assign domain (some value))).bind
                  fun permutation => eager value permutation) :=
              compatibleLaw_forward assign injective domain pinned eager
          _ = (freshValueLaw assign).bind (fun value =>
                lazy value (Function.update assign domain (some value))) := by
              refine bind_congr_support fun value member => ?_
              exact step value (Function.update assign domain (some value))
                (update_injective assign injective domain value
                  (freshValueLaw_support assign
                    (unused_nonempty assign injective domain pinned) member))
          _ = (lazyAnswer queryIndex state.view (PublicQuery.fixedForward queryIndex domain)
                assign).bind fun pair => lazy pair.1 pair.2 := by
              rw [lazyEq]
              exact (bind_of_map (freshValueLaw assign)
                (fun value => (value, Function.update assign domain (some value)))
                fun pair => lazy pair.1 pair.2).symm
    · have lazyEq : lazyAnswer index state.view (PublicQuery.fixedForward queryIndex domain)
          assign =
          PMF.pure (publicAnswer state.view (PublicQuery.fixedForward queryIndex domain),
            assign) := by
        simp only [lazyAnswer, if_neg tracked]
        rfl
      calc ((compatibleLaw assign).bind fun permutation =>
            eager (publicAnswer (setPermutation state index permutation).view
              (PublicQuery.fixedForward queryIndex domain)) permutation)
          = (compatibleLaw assign).bind (fun permutation =>
              eager (publicAnswer state.view (PublicQuery.fixedForward queryIndex domain))
                permutation) := by
            refine congrArg (PMF.bind _) (funext fun permutation => ?_)
            rw [publicAnswer_setPermutation_forward_of_ne _ _ _ _ _ tracked]
        _ = lazy (publicAnswer state.view (PublicQuery.fixedForward queryIndex domain)) assign :=
            step (publicAnswer state.view (PublicQuery.fixedForward queryIndex domain)) assign
              injective
        _ = (lazyAnswer index state.view (PublicQuery.fixedForward queryIndex domain) assign).bind
              fun pair => lazy pair.1 pair.2 := by
            rw [lazyEq]
            exact (PMF.pure_bind
              (publicAnswer state.view (PublicQuery.fixedForward queryIndex domain), assign)
              fun pair => lazy pair.1 pair.2).symm
  | fixedInverse queryIndex range =>
    by_cases tracked : queryIndex = index
    · subst tracked
      cases transposed : pinnedInput assign range with
      | some domain =>
        have pin := (pinnedInput_eq_some_iff assign injective range domain).mp transposed
        have lazyEq : lazyAnswer queryIndex state.view
            (PublicQuery.fixedInverse queryIndex range) assign = PMF.pure (domain, assign) := by
          simp [lazyAnswer, transposed]
          rfl
        calc ((compatibleLaw assign).bind fun permutation =>
              eager (publicAnswer (setPermutation state queryIndex permutation).view
                (PublicQuery.fixedInverse queryIndex range)) permutation)
            = (compatibleLaw assign).bind (fun permutation => eager domain permutation) := by
              refine bind_congr_support fun permutation member => ?_
              rw [publicAnswer_setPermutation_inverse,
                ← compatibleLaw_support assign injective member domain range pin,
                Equiv.symm_apply_apply]
          _ = lazy domain assign := step domain assign injective
          _ = (lazyAnswer queryIndex state.view (PublicQuery.fixedInverse queryIndex range)
                assign).bind fun pair => lazy pair.1 pair.2 := by
              rw [lazyEq]
              exact (PMF.pure_bind (domain, assign) fun pair => lazy pair.1 pair.2).symm
      | none =>
        have fresh := notMem_pinnedRange_of_pinnedInput_eq_none assign injective transposed
        have lazyEq : lazyAnswer queryIndex state.view
            (PublicQuery.fixedInverse queryIndex range) assign =
            (freshInputLaw assign).map fun domain =>
              (domain, Function.update assign domain (some range)) := by
          simp [lazyAnswer, transposed]
          rfl
        calc ((compatibleLaw assign).bind fun permutation =>
              eager (publicAnswer (setPermutation state queryIndex permutation).view
                (PublicQuery.fixedInverse queryIndex range)) permutation)
            = (compatibleLaw assign).bind (fun permutation =>
                eager (permutation.symm range) permutation) := by
              refine congrArg (PMF.bind _) (funext fun permutation => ?_)
              rw [publicAnswer_setPermutation_inverse]
          _ = (freshInputLaw assign).bind (fun domain =>
                (compatibleLaw (Function.update assign domain (some range))).bind
                  fun permutation => eager domain permutation) :=
              compatibleLaw_inverse assign injective range fresh eager
          _ = (freshInputLaw assign).bind (fun domain =>
                lazy domain (Function.update assign domain (some range))) := by
              refine congrArg (PMF.bind _) (funext fun domain => ?_)
              exact step domain (Function.update assign domain (some range))
                (update_injective assign injective domain range fresh)
          _ = (lazyAnswer queryIndex state.view (PublicQuery.fixedInverse queryIndex range)
                assign).bind fun pair => lazy pair.1 pair.2 := by
              rw [lazyEq]
              exact (bind_of_map (freshInputLaw assign)
                (fun domain => (domain, Function.update assign domain (some range)))
                fun pair => lazy pair.1 pair.2).symm
    · have lazyEq : lazyAnswer index state.view (PublicQuery.fixedInverse queryIndex range)
          assign =
          PMF.pure (publicAnswer state.view (PublicQuery.fixedInverse queryIndex range),
            assign) := by
        simp only [lazyAnswer, if_neg tracked]
        rfl
      calc ((compatibleLaw assign).bind fun permutation =>
            eager (publicAnswer (setPermutation state index permutation).view
              (PublicQuery.fixedInverse queryIndex range)) permutation)
          = (compatibleLaw assign).bind (fun permutation =>
              eager (publicAnswer state.view (PublicQuery.fixedInverse queryIndex range))
                permutation) := by
            refine congrArg (PMF.bind _) (funext fun permutation => ?_)
            rw [publicAnswer_setPermutation_inverse_of_ne _ _ _ _ _ tracked]
        _ = lazy (publicAnswer state.view (PublicQuery.fixedInverse queryIndex range)) assign :=
            step (publicAnswer state.view (PublicQuery.fixedInverse queryIndex range)) assign
              injective
        _ = (lazyAnswer index state.view (PublicQuery.fixedInverse queryIndex range) assign).bind
              fun pair => lazy pair.1 pair.2 := by
            rw [lazyEq]
            exact (PMF.pure_bind
              (publicAnswer state.view (PublicQuery.fixedInverse queryIndex range), assign)
              fun pair => lazy pair.1 pair.2).symm
  | encForward queryIndex domain =>
    calc ((compatibleLaw assign).bind fun permutation =>
          eager (publicAnswer (setPermutation state index permutation).view
            (PublicQuery.encForward queryIndex domain)) permutation)
        = lazy (publicAnswer state.view (PublicQuery.encForward queryIndex domain)) assign :=
          step (publicAnswer state.view (PublicQuery.encForward queryIndex domain)) assign
            injective
      _ = (lazyAnswer index state.view (PublicQuery.encForward queryIndex domain) assign).bind
            fun pair => lazy pair.1 pair.2 :=
          (PMF.pure_bind
            (publicAnswer state.view (PublicQuery.encForward queryIndex domain), assign)
            fun pair => lazy pair.1 pair.2).symm
  | encInverse queryIndex range =>
    calc ((compatibleLaw assign).bind fun permutation =>
          eager (publicAnswer (setPermutation state index permutation).view
            (PublicQuery.encInverse queryIndex range)) permutation)
        = lazy (publicAnswer state.view (PublicQuery.encInverse queryIndex range)) assign :=
          step (publicAnswer state.view (PublicQuery.encInverse queryIndex range)) assign
            injective
      _ = (lazyAnswer index state.view (PublicQuery.encInverse queryIndex range) assign).bind
            fun pair => lazy pair.1 pair.2 :=
          (PMF.pure_bind
            (publicAnswer state.view (PublicQuery.encInverse queryIndex range), assign)
            fun pair => lazy pair.1 pair.2).symm
  | hash point =>
    calc ((compatibleLaw assign).bind fun permutation =>
          eager (publicAnswer (setPermutation state index permutation).view
            (PublicQuery.hash point)) permutation)
        = lazy (publicAnswer state.view (PublicQuery.hash point)) assign :=
          step (publicAnswer state.view (PublicQuery.hash point)) assign injective
      _ = (lazyAnswer index state.view (PublicQuery.hash point) assign).bind
            fun pair => lazy pair.1 pair.2 :=
          (PMF.pure_bind (publicAnswer state.view (PublicQuery.hash point), assign)
            fun pair => lazy pair.1 pair.2).symm



/-- The eager model and the lazy model give the same law of the result, the log and the tracked
permutation: sampling the whole permutation before the run is the same as sampling only its
transcript during the run and the permutation afterwards, conditioned on that transcript. -/
theorem compatibleLaw_run {Result : Type} {budget : Nat} (index : FixedKeyIndex)
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget) :
    ∀ (state : State) (assign : Assignment), AssignmentInjective assign →
      ((compatibleLaw assign).bind fun permutation =>
          (program.run idealOracle (setPermutation state index permutation)).map fun output =>
            ((output.1, output.2.log), permutation)) =
        (lazyRun index program state assign).bind fun output =>
          (compatibleLaw output.2).map fun permutation => (output.1, permutation) := by
  induction program with
  | pure distribution =>
    intro state assign injective
    have lhs : ((compatibleLaw assign).bind fun permutation =>
          ((OracleProgram.pure (oracle := publicOracleSpec FixedKeyIndex Garbling.EncIndex)
              (budget := budget) distribution).run idealOracle
              (setPermutation state index permutation)).map
            fun output => ((output.1, output.2.log), permutation)) =
        (compatibleLaw assign).bind fun permutation =>
          distribution.bind fun value => PMF.pure ((value, state.log), permutation) := by
      refine congrArg (PMF.bind _) (funext fun permutation => ?_)
      rw [OracleProgram.run_pure, PMF.map, PMF.map, PMF.bind_bind]
      exact congrArg (PMF.bind _) (funext fun value => PMF.pure_bind _ _)
    have rhs : ((lazyRun index (OracleProgram.pure (budget := budget) distribution) state
          assign).bind fun output =>
            (compatibleLaw output.2).map fun permutation => (output.1, permutation)) =
        distribution.bind fun value => (compatibleLaw assign).bind fun permutation =>
          PMF.pure ((value, state.log), permutation) := by
      show ((distribution.map fun value => ((value, state.log), assign)).bind fun output =>
        (compatibleLaw output.2).map fun permutation => (output.1, permutation)) = _
      rw [bind_of_map]
      exact congrArg (PMF.bind _) (funext fun value => rfl)
    exact lhs.trans ((PMF.bind_comm _ _ _).trans rhs.symm)
  | query request next inductionHypothesis =>
    intro state assign injective
    have lhs : ((compatibleLaw assign).bind fun permutation =>
          ((OracleProgram.query request next).run idealOracle
            (setPermutation state index permutation)).map fun output =>
              ((output.1, output.2.log), permutation)) =
        (compatibleLaw assign).bind fun permutation =>
          ((next (publicAnswer (setPermutation state index permutation).view request)).run
              idealOracle
              (setPermutation { state with log := request :: state.log } index permutation)).map
            fun output => ((output.1, output.2.log), permutation) := by
      refine congrArg (PMF.bind _) (funext fun permutation => ?_)
      rw [OracleProgram.run_query]
      rfl
    have rhs : ((lazyRun index (OracleProgram.query request next) state assign).bind fun output =>
          (compatibleLaw output.2).map fun permutation => (output.1, permutation)) =
        (lazyAnswer index state.view request assign).bind fun pair =>
          (lazyRun index (next pair.1) { state with log := request :: state.log } pair.2).bind
            fun output => (compatibleLaw output.2).map fun permutation =>
              (output.1, permutation) :=
      PMF.bind_bind _ _ _
    refine lhs.trans (Eq.trans ?_ rhs.symm)
    exact lazy_query_step index request state assign injective
      (fun answer permutation => ((next answer).run idealOracle
        (setPermutation { state with log := request :: state.log } index permutation)).map
          fun output => ((output.1, output.2.log), permutation))
      (fun answer other => (lazyRun index (next answer)
        { state with log := request :: state.log } other).bind fun output =>
          (compatibleLaw output.2).map fun permutation => (output.1, permutation))
      fun answer other injectiveOther =>
        inductionHypothesis answer { state with log := request :: state.log } other injectiveOther
  | sample distribution next inductionHypothesis =>
    intro state assign injective
    have lhs : ((compatibleLaw assign).bind fun permutation =>
          ((OracleProgram.sample distribution next).run idealOracle
            (setPermutation state index permutation)).map fun output =>
              ((output.1, output.2.log), permutation)) =
        (compatibleLaw assign).bind fun permutation => distribution.bind fun value =>
          ((next value).run idealOracle (setPermutation state index permutation)).map
            fun output => ((output.1, output.2.log), permutation) := by
      refine congrArg (PMF.bind _) (funext fun permutation => ?_)
      rw [OracleProgram.run_sample, PMF.map_bind]
    have rhs : ((lazyRun index (OracleProgram.sample distribution next) state assign).bind
          fun output =>
            (compatibleLaw output.2).map fun permutation => (output.1, permutation)) =
        distribution.bind fun value => (lazyRun index (next value) state assign).bind
          fun output => (compatibleLaw output.2).map fun permutation =>
            (output.1, permutation) :=
      PMF.bind_bind _ _ _
    refine lhs.trans (Eq.trans ((PMF.bind_comm _ _ _).trans ?_) rhs.symm)
    exact congrArg (PMF.bind _)
      (funext fun value => inductionHypothesis value state assign injective)

/-! ### Conditional uniformity -/

/-- The number of points a transcript has pinned. -/
def pinnedCount (assign : Assignment) : Nat := (pinnedDomain assign).ncard

theorem card_pinnedDomain_eq (assign : Assignment) :
    Fintype.card (pinnedDomain assign) = pinnedCount assign := by
  rw [pinnedCount, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

theorem pinnedDomain_update (assign : Assignment) (input value : Block) :
    pinnedDomain (Function.update assign input (some value)) =
      insert input (pinnedDomain assign) := by
  ext other
  by_cases same : other = input
  · subst same
    simp [pinnedDomain]
  · simp [pinnedDomain, Function.update_of_ne same, same]

theorem pinnedCount_update_le (assign : Assignment) (input value : Block) :
    pinnedCount (Function.update assign input (some value)) ≤ pinnedCount assign + 1 := by
  rw [pinnedCount, pinnedDomain_update]
  exact Set.ncard_insert_le input (pinnedDomain assign)

/-- An injective transcript leaves exactly the values it has not pinned. -/
theorem card_unused (assign : Assignment) (injective : AssignmentInjective assign) :
    Fintype.card {value : Block // value ∉ pinnedRange assign} =
      Fintype.card Block - pinnedCount assign := by
  have bridge : Fintype.card {value : Block // value ∈ pinnedRange assign} =
      Fintype.card (pinnedRange assign) := Fintype.card_congr (Equiv.refl _)
  rw [Fintype.card_subtype_compl (p := fun value => value ∈ pinnedRange assign), bridge,
    card_pinnedRange assign injective, card_pinnedDomain_eq]

/-- Conditionally on a transcript, the tracked permutation's value at an unpinned input is
uniform over the values the transcript has not pinned. -/
theorem compatibleLaw_map_apply (assign : Assignment) (injective : AssignmentInjective assign)
    (input : Block) (fresh : assign input = none) :
    ((compatibleLaw assign).map fun permutation => permutation input) = freshValueLaw assign := by
  have forward := compatibleLaw_forward assign injective input fresh
    (fun value _ => PMF.pure value)
  rw [PMF.map, Function.comp_def]
  refine forward.trans ?_
  refine (congrArg (PMF.bind _) (funext fun value => PMF.bind_const _ _)).trans ?_
  exact PMF.bind_pure _

/-- Conditionally on a transcript, the tracked permutation's preimage of an unpinned value is
uniform over the inputs the transcript has not pinned. -/
theorem compatibleLaw_map_symm_apply (assign : Assignment)
    (injective : AssignmentInjective assign) (value : Block)
    (fresh : value ∉ pinnedRange assign) :
    ((compatibleLaw assign).map fun permutation => permutation.symm value) =
      freshInputLaw assign := by
  have inverse := compatibleLaw_inverse assign injective value fresh
    (fun input _ => PMF.pure input)
  rw [PMF.map, Function.comp_def]
  refine inverse.trans ?_
  refine (congrArg (PMF.bind _) (funext fun input => PMF.bind_const _ _)).trans ?_
  exact PMF.bind_pure _

theorem uniform_map_val_apply_le {Value : Type} {predicate : Value → Prop}
    [Fintype {value // predicate value}] [Nonempty {value // predicate value}] (point : Value) :
    ((PMF.uniformOfFintype {value // predicate value}).map Subtype.val) point ≤
      (Fintype.card {value // predicate value} : ENNReal)⁻¹ := by
  rw [PMF.map_apply]
  by_cases holds : predicate point
  · rw [tsum_eq_single ⟨point, holds⟩ fun other different =>
      if_neg fun same => different (Subtype.ext same.symm), if_pos rfl]
    exact le_of_eq (PMF.uniformOfFintype_apply _)
  · refine le_trans (le_of_eq ?_) (zero_le)
    refine ENNReal.tsum_eq_zero.mpr fun other => if_neg ?_
    rintro rfl
    exact holds other.2

/-- A transcript of at most `budget` pinned points leaves the tracked permutation's value at an
unpinned input uniform over at least `2 ^ 128 - budget` values, so it takes any given value with
probability at most `1 / (2 ^ 128 - budget)`. -/
theorem compatibleLaw_apply_le (assign : Assignment) (injective : AssignmentInjective assign)
    (input : Block) (fresh : assign input = none) (budget : Nat)
    (small : pinnedCount assign ≤ budget) (value : Block) :
    ((compatibleLaw assign).map fun permutation => permutation input) value ≤
      (((2 ^ 128 - budget : Nat) : ENNReal))⁻¹ := by
  haveI unused := unused_nonempty assign injective input fresh
  rw [compatibleLaw_map_apply assign injective input fresh, freshValueLaw_eq assign unused]
  refine le_trans (uniform_map_val_apply_le value) ?_
  refine ENNReal.inv_le_inv.mpr ?_
  rw [card_unused assign injective, card_block]
  exact Nat.cast_le.mpr (Nat.sub_le_sub_left small _)

/-- The same bound for the preimage of an unpinned value. -/
theorem compatibleLaw_symm_apply_le (assign : Assignment)
    (injective : AssignmentInjective assign) (value : Block)
    (fresh : value ∉ pinnedRange assign) (budget : Nat) (small : pinnedCount assign ≤ budget)
    (input : Block) :
    ((compatibleLaw assign).map fun permutation => permutation.symm value) input ≤
      (((2 ^ 128 - budget : Nat) : ENNReal))⁻¹ := by
  haveI unpinned := unpinned_nonempty assign injective value fresh
  haveI offDomain : Nonempty {point : Block // point ∉ pinnedDomain assign} := by
    obtain ⟨witness⟩ := unpinned
    exact ⟨⟨witness.1, notMem_pinnedDomain witness.2⟩⟩
  rw [compatibleLaw_map_symm_apply assign injective value fresh,
    freshInputLaw_eq assign unpinned]
  refine le_trans (uniform_map_val_apply_le input) ?_
  refine ENNReal.inv_le_inv.mpr ?_
  have count : Fintype.card {point : Block // assign point = none} =
      Fintype.card Block - pinnedCount assign := by
    have bridge : Fintype.card {point : Block // point ∈ pinnedDomain assign} =
        Fintype.card (pinnedDomain assign) := Fintype.card_congr (Equiv.refl _)
    have same : Fintype.card {point : Block // assign point = none} =
        Fintype.card {point : Block // point ∉ pinnedDomain assign} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun point =>
        ⟨fun none => notMem_pinnedDomain none, fun off => eq_none_of_notMem_pinnedDomain off⟩)
    rw [same, Fintype.card_subtype_compl (p := fun point => point ∈ pinnedDomain assign), bridge,
      card_pinnedDomain_eq]
  rw [count, card_block]
  exact Nat.cast_le.mpr (Nat.sub_le_sub_left small _)


/-! ### The transcript grows by at most one pin per query -/

theorem eq_of_mem_support_pure {Value : Type} {point other : Value}
    (member : point ∈ (PMF.pure other).support) : point = other := by
  rw [PMF.mem_support_iff, PMF.pure_apply] at member
  by_contra different
  exact member (if_neg different)

theorem exists_of_mem_support_map {Value Other : Type} {law : PMF Value} {step : Value → Other}
    {point : Other} (member : point ∈ (law.map step).support) : ∃ value, step value = point := by
  rw [PMF.support_map] at member
  obtain ⟨value, _, equal⟩ := member
  exact ⟨value, equal⟩

theorem lazyAnswer_pinnedCount (index : FixedKeyIndex) (view : View) (request : Query)
    (assign : Assignment) (pair : request.Answer × Assignment)
    (member : pair ∈ (lazyAnswer index view request assign).support) :
    pinnedCount pair.2 ≤ pinnedCount assign + 1 := by
  cases request with
  | fixedForward queryIndex domain =>
    by_cases tracked : queryIndex = index
    · subst tracked
      cases pinned : assign domain with
      | some value =>
        have lazyEq : lazyAnswer queryIndex view (PublicQuery.fixedForward queryIndex domain)
            assign = PMF.pure (value, assign) := by
          simp [lazyAnswer, pinned]
          rfl
        rw [lazyEq] at member
        rw [eq_of_mem_support_pure member]
        exact Nat.le_succ _
      | none =>
        have lazyEq : lazyAnswer queryIndex view (PublicQuery.fixedForward queryIndex domain)
            assign = (freshValueLaw assign).map fun value =>
              (value, Function.update assign domain (some value)) := by
          simp [lazyAnswer, pinned]
          rfl
        rw [lazyEq] at member
        obtain ⟨value, equal⟩ := exists_of_mem_support_map member
        rw [← equal]
        exact pinnedCount_update_le assign domain value
    · have lazyEq : lazyAnswer index view (PublicQuery.fixedForward queryIndex domain) assign =
          PMF.pure (publicAnswer view (PublicQuery.fixedForward queryIndex domain), assign) := by
        simp only [lazyAnswer, if_neg tracked]
        rfl
      rw [lazyEq] at member
      rw [eq_of_mem_support_pure member]
      exact Nat.le_succ _
  | fixedInverse queryIndex range =>
    by_cases tracked : queryIndex = index
    · subst tracked
      cases transposed : pinnedInput assign range with
      | some domain =>
        have lazyEq : lazyAnswer queryIndex view (PublicQuery.fixedInverse queryIndex range)
            assign = PMF.pure (domain, assign) := by
          simp [lazyAnswer, transposed]
          rfl
        rw [lazyEq] at member
        rw [eq_of_mem_support_pure member]
        exact Nat.le_succ _
      | none =>
        have lazyEq : lazyAnswer queryIndex view (PublicQuery.fixedInverse queryIndex range)
            assign = (freshInputLaw assign).map fun domain =>
              (domain, Function.update assign domain (some range)) := by
          simp [lazyAnswer, transposed]
          rfl
        rw [lazyEq] at member
        obtain ⟨domain, equal⟩ := exists_of_mem_support_map member
        rw [← equal]
        exact pinnedCount_update_le assign domain range
    · have lazyEq : lazyAnswer index view (PublicQuery.fixedInverse queryIndex range) assign =
          PMF.pure (publicAnswer view (PublicQuery.fixedInverse queryIndex range), assign) := by
        simp only [lazyAnswer, if_neg tracked]
        rfl
      rw [lazyEq] at member
      rw [eq_of_mem_support_pure member]
      exact Nat.le_succ _
  | encForward queryIndex domain =>
    have lazyEq : lazyAnswer index view (PublicQuery.encForward queryIndex domain) assign =
        PMF.pure (publicAnswer view (PublicQuery.encForward queryIndex domain), assign) := rfl
    rw [lazyEq] at member
    rw [eq_of_mem_support_pure member]
    exact Nat.le_succ _
  | encInverse queryIndex range =>
    have lazyEq : lazyAnswer index view (PublicQuery.encInverse queryIndex range) assign =
        PMF.pure (publicAnswer view (PublicQuery.encInverse queryIndex range), assign) := rfl
    rw [lazyEq] at member
    rw [eq_of_mem_support_pure member]
    exact Nat.le_succ _
  | hash point =>
    have lazyEq : lazyAnswer index view (PublicQuery.hash point) assign =
        PMF.pure (publicAnswer view (PublicQuery.hash point), assign) := rfl
    rw [lazyEq] at member
    rw [eq_of_mem_support_pure member]
    exact Nat.le_succ _

/-- A lazy run of a program with `budget` queries pins at most `budget` further points. -/
theorem lazyRun_pinnedCount {Result : Type} {budget : Nat} (index : FixedKeyIndex)
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget) :
    ∀ (state : State) (assign : Assignment) (output : (Result × List Query) × Assignment),
      output ∈ (lazyRun index program state assign).support →
        pinnedCount output.2 ≤ pinnedCount assign + budget := by
  induction program with
  | pure distribution =>
    intro state assign output member
    rw [lazyRun, PMF.support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact Nat.le_add_right _ _
  | query request next inductionHypothesis =>
    intro state assign output member
    rw [lazyRun, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨pair, pairMember, member⟩ := member
    have tail := inductionHypothesis pair.1 { state with log := request :: state.log } pair.2
      output member
    have head := lazyAnswer_pinnedCount index state.view request assign pair pairMember
    omega
  | sample distribution next inductionHypothesis =>
    intro state assign output member
    rw [lazyRun, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨value, _, member⟩ := member
    exact inductionHypothesis value state assign output member


end

end Kriterion.ArgoMAC.Security
