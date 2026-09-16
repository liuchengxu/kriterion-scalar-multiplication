/-
This file proves the independence bad-bounds. A logged run that never reads a
label hits a set of points determined by that label with probability at most
the number of points times the log length over `2^128`: the label is sampled
after the run, a union bound runs over the log entries, and each entry hits
each point with probability exactly `1 / 2^128` because one label of a uniform
label key is a uniform block. The file also identifies the points at which
programming one permutation at one label changes a public answer: two label
values per forward query and two per inverse query.
-/

import Proof.ReferenceGame
import Proof.Programming

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-! ### The union bound over a log -/

/-- The mass of "some entry is bad" is at most the sum over the entries. -/
theorem toOuterMeasure_exists_mem_le {Sample Entry : Type} (law : PMF Sample)
    (entries : List Entry) (bad : Entry → Set Sample) :
    law.toOuterMeasure {sample | ∃ entry ∈ entries, sample ∈ bad entry} ≤
      (entries.map fun entry => law.toOuterMeasure (bad entry)).sum := by
  induction entries with
  | nil =>
    simp only [List.not_mem_nil, false_and, exists_false, Set.ofPred_false, List.map_nil,
      List.sum_nil]
    exact le_of_eq (MeasureTheory.measure_empty (μ := law.toOuterMeasure))
  | cons entry rest inductionHypothesis =>
    have split : {sample | ∃ entry' ∈ entry :: rest, sample ∈ bad entry'} =
        bad entry ∪ {sample | ∃ entry' ∈ rest, sample ∈ bad entry'} := by
      ext sample
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨entry', head | tail, member⟩
        · exact Or.inl (head ▸ member)
        · exact Or.inr ⟨entry', tail, member⟩
      · rintro (member | ⟨entry', tail, member⟩)
        · exact ⟨entry, Or.inl rfl, member⟩
        · exact ⟨entry', Or.inr tail, member⟩
    rw [split, List.map_cons, List.sum_cons]
    exact (MeasureTheory.measure_union_le _ _).trans (add_le_add le_rfl inductionHypothesis)

/-- With every entry bad with mass at most `ε`, "some entry is bad" has mass at most the
length times `ε`. -/
theorem toOuterMeasure_exists_mem_le_of_le {Sample Entry : Type} (law : PMF Sample)
    (entries : List Entry) (bad : Entry → Set Sample) (bound : ENNReal)
    (each : ∀ entry ∈ entries, law.toOuterMeasure (bad entry) ≤ bound) :
    law.toOuterMeasure {sample | ∃ entry ∈ entries, sample ∈ bad entry} ≤
      entries.length * bound := by
  refine (toOuterMeasure_exists_mem_le law entries bad).trans ?_
  induction entries with
  | nil => simp
  | cons entry rest inductionHypothesis =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ, add_mul, one_mul,
      add_comm]
    exact add_le_add
      (inductionHypothesis fun entry' member => each entry' (List.mem_cons_of_mem _ member))
      (each entry List.mem_cons_self)

/-- A run that never reads the label, followed by a fresh label: the mass of "some log
entry is bad for the label" is at most the budget times the worst entry mass. -/
theorem hidden_label_bound {Data Outcome Label Entry : Type} (data : PMF Data)
    (run : Data → PMF Outcome) (labels : PMF Label) (log : Data → Outcome → List Entry)
    (bad : Data → Outcome → Entry → Set Label) (budget : Nat) (bound : ENNReal)
    (lengthLe : ∀ datum, ∀ outcome ∈ (run datum).support, (log datum outcome).length ≤ budget)
    (entryLe : ∀ datum outcome entry, labels.toOuterMeasure (bad datum outcome entry) ≤ bound) :
    (data.bind fun datum => (run datum).bind fun outcome =>
        labels.map fun label => (datum, outcome, label)).toOuterMeasure
      {triple | ∃ entry ∈ log triple.1 triple.2.1, triple.2.2 ∈ bad triple.1 triple.2.1 entry} ≤
      budget * bound := by
  refine Probability.bind_event_le _ _ _ _ fun datum _ => ?_
  refine Probability.bind_event_le _ _ _ _ fun outcome member => ?_
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (toOuterMeasure_exists_mem_le_of_le labels (log datum outcome)
    (bad datum outcome) bound fun entry _ => entryLe datum outcome entry) ?_
  exact mul_le_mul' (Nat.cast_le.mpr (lengthLe datum outcome member)) le_rfl

/-! ### One label of a uniform label key is a uniform block -/

/-- The coordinate key an adaptor reads: `false` for `x`, `true` for `y`. -/
def adaptorCoordinate : CurveAdaptor → Bool
  | .y4 | .y6 => true
  | .x3 | .x5 | .x7 => false

/-- The label key of one coordinate. -/
def coordinateKey (key : InputMacKey) : Bool → CoordinateMacKey
  | false => key.x
  | true => key.y

theorem gateKey_eq (key : InputMacKey) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) :
    gateKey key adaptor position = (coordinateKey key (adaptorCoordinate adaptor)).get position := by
  cases adaptor <;> rfl

/-- One label of the key: a coordinate, a position, and which of the two labels. -/
def keyLabel (key : InputMacKey) (coordinate : Bool) (position : Fin coordinateBitCount)
    (value : Bool) : Block :=
  BitAdaptor.encode ((coordinateKey key coordinate).get position) value

theorem selectedLabel_eq (key : InputMacKey) (input : AffineInput) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) :
    selectedLabel key input adaptor position =
      keyLabel key (adaptorCoordinate adaptor) position (inputBits input adaptor position) := by
  unfold selectedLabel keyLabel
  rw [gateKey_eq]

/-- Replace one label of a label pair. -/
def setPairLabel (pair : BitAdaptor.Key) (value : Bool) (label : Block) : BitAdaptor.Key :=
  if value then { pair with trueLabel := label } else { pair with falseLabel := label }

theorem encode_setPairLabel (pair : BitAdaptor.Key) (value : Bool) (label : Block) :
    BitAdaptor.encode (setPairLabel pair value label) value = label := by
  cases value <;> rfl

theorem setPairLabel_encode (pair : BitAdaptor.Key) (value : Bool) :
    setPairLabel pair value (BitAdaptor.encode pair value) = pair := by
  cases value <;> rfl

theorem setPairLabel_setPairLabel (pair : BitAdaptor.Key) (value : Bool) (first second : Block) :
    setPairLabel (setPairLabel pair value first) value second = setPairLabel pair value second := by
  cases value <;> rfl

/-- Replace one label of a coordinate key. -/
def setCoordinateLabel (key : CoordinateMacKey) (position : Fin coordinateBitCount)
    (value : Bool) (label : Block) : CoordinateMacKey :=
  key.set position (setPairLabel (key.get position) value label)

theorem Vector.get_eq_getElem {Value : Type} {count : Nat} (values : Vector Value count)
    (index : Fin count) : values.get index = values[index.val] := rfl

theorem get_setCoordinateLabel (key : CoordinateMacKey) (position : Fin coordinateBitCount)
    (value : Bool) (label : Block) :
    (setCoordinateLabel key position value label).get position =
      setPairLabel (key.get position) value label := by
  unfold setCoordinateLabel
  rw [Vector.get_eq_getElem, Vector.getElem_set_self]

theorem setCoordinateLabel_get (key : CoordinateMacKey) (position : Fin coordinateBitCount)
    (value : Bool) :
    setCoordinateLabel key position value (BitAdaptor.encode (key.get position) value) = key := by
  unfold setCoordinateLabel
  rw [setPairLabel_encode, Vector.get_eq_getElem, Vector.set_getElem_self]

theorem setCoordinateLabel_setCoordinateLabel (key : CoordinateMacKey)
    (position : Fin coordinateBitCount) (value : Bool) (first second : Block) :
    setCoordinateLabel (setCoordinateLabel key position value first) position value second =
      setCoordinateLabel key position value second := by
  unfold setCoordinateLabel
  simp only [Vector.get_eq_getElem, Vector.getElem_set_self, setPairLabel_setPairLabel,
    Vector.set_set]

/-- Replace one label of the key. -/
def setKeyLabel (key : InputMacKey) (coordinate : Bool) (position : Fin coordinateBitCount)
    (value : Bool) (label : Block) : InputMacKey :=
  match coordinate with
  | false => { key with x := setCoordinateLabel key.x position value label }
  | true => { key with y := setCoordinateLabel key.y position value label }

theorem coordinateKey_setKeyLabel (key : InputMacKey) (coordinate : Bool)
    (position : Fin coordinateBitCount) (value : Bool) (label : Block) :
    coordinateKey (setKeyLabel key coordinate position value label) coordinate =
      setCoordinateLabel (coordinateKey key coordinate) position value label := by
  cases coordinate <;> rfl

theorem keyLabel_setKeyLabel (key : InputMacKey) (coordinate : Bool)
    (position : Fin coordinateBitCount) (value : Bool) (label : Block) :
    keyLabel (setKeyLabel key coordinate position value label) coordinate position value =
      label := by
  unfold keyLabel
  rw [coordinateKey_setKeyLabel, get_setCoordinateLabel, encode_setPairLabel]

theorem setKeyLabel_keyLabel (key : InputMacKey) (coordinate : Bool)
    (position : Fin coordinateBitCount) (value : Bool) :
    setKeyLabel key coordinate position value (keyLabel key coordinate position value) = key := by
  cases coordinate <;> simp only [setKeyLabel, keyLabel, coordinateKey, setCoordinateLabel_get]

theorem setKeyLabel_setKeyLabel (key : InputMacKey) (coordinate : Bool)
    (position : Fin coordinateBitCount) (value : Bool) (first second : Block) :
    setKeyLabel (setKeyLabel key coordinate position value first) coordinate position value
      second = setKeyLabel key coordinate position value second := by
  cases coordinate <;> simp only [setKeyLabel, setCoordinateLabel_setCoordinateLabel]

/-- Exchanging one label of the key with a separate block is an involution. -/
def swapKeyLabel (coordinate : Bool) (position : Fin coordinateBitCount) (value : Bool) :
    InputMacKey × Block ≃ InputMacKey × Block where
  toFun pair := (setKeyLabel pair.1 coordinate position value pair.2,
    keyLabel pair.1 coordinate position value)
  invFun pair := (setKeyLabel pair.1 coordinate position value pair.2,
    keyLabel pair.1 coordinate position value)
  left_inv pair := by
    obtain ⟨key, label⟩ := pair
    simp only [Prod.mk.injEq]
    exact ⟨by rw [setKeyLabel_setKeyLabel, setKeyLabel_keyLabel], keyLabel_setKeyLabel _ _ _ _ _⟩
  right_inv pair := by
    obtain ⟨key, label⟩ := pair
    simp only [Prod.mk.injEq]
    exact ⟨by rw [setKeyLabel_setKeyLabel, setKeyLabel_keyLabel], keyLabel_setKeyLabel _ _ _ _ _⟩

instance : Nonempty InputMacKey := ⟨witnessTape.inputMacKey⟩

/-- A uniform key with one label replaced by a fresh uniform block is a uniform key. -/
theorem uniform_bind_setKeyLabel {Outcome : Type} (coordinate : Bool)
    (position : Fin coordinateBitCount) (value : Bool)
    (continuation : InputMacKey → PMF Outcome) :
    ((PMF.uniformOfFintype InputMacKey).bind fun key =>
        (PMF.uniformOfFintype Block).bind fun label =>
          continuation (setKeyLabel key coordinate position value label)) =
      (PMF.uniformOfFintype InputMacKey).bind continuation := by
  rw [uniformOfFintype_bind_prod]
  have swapped := uniformOfFintype_bind_equiv (swapKeyLabel coordinate position value)
    (fun pair : InputMacKey × Block => continuation pair.1)
  simp only [swapKeyLabel, Equiv.coe_fn_mk] at swapped
  have unprod : ((PMF.uniformOfFintype (InputMacKey × Block)).bind fun pair =>
      continuation pair.1) =
      (PMF.uniformOfFintype InputMacKey).bind fun key =>
        (PMF.uniformOfFintype Block).bind fun _ => continuation key :=
    (uniformOfFintype_bind_prod fun key (_ : Block) => continuation key).symm
  rw [swapped, unprod]
  simp only [PMF.bind_const]

/-- One label of a uniform key is a uniform block. -/
theorem map_keyLabel_uniform (coordinate : Bool) (position : Fin coordinateBitCount)
    (value : Bool) :
    (PMF.uniformOfFintype InputMacKey).map (fun key => keyLabel key coordinate position value) =
      PMF.uniformOfFintype Block := by
  change (PMF.uniformOfFintype InputMacKey).bind
    (PMF.pure ∘ fun key => keyLabel key coordinate position value) = _
  rw [← uniform_bind_setKeyLabel coordinate position value]
  simp only [Function.comp_def, keyLabel_setKeyLabel, PMF.bind_pure, PMF.bind_const]

/-- The mass of a finite set of blocks under the uniform block law. -/
theorem uniform_block_toOuterMeasure (points : Finset Block) :
    (PMF.uniformOfFintype Block).toOuterMeasure points = points.card / 2 ^ 128 := by
  rw [PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul]
  have card : (Fintype.card Block : ENNReal) = 2 ^ 128 := by
    rw [show Fintype.card Block = 2 ^ 128 from (Fintype.ofEquiv_card _).trans (Fintype.card_fin _)]
    exact Nat.cast_pow 2 128
  rw [card, div_eq_mul_inv]

/-- One label of a uniform key lies in a finite set of blocks with the mass of that set. -/
theorem uniform_keyLabel_mem (coordinate : Bool) (position : Fin coordinateBitCount)
    (value : Bool) (points : Finset Block) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
        {key | keyLabel key coordinate position value ∈ points} = points.card / 2 ^ 128 := by
  have preimage : {key | keyLabel key coordinate position value ∈ points} =
      (fun key => keyLabel key coordinate position value) ⁻¹' (points : Set Block) := rfl
  rw [preimage, ← PMF.toOuterMeasure_map_apply, map_keyLabel_uniform,
    uniform_block_toOuterMeasure]

/-! ### The hidden points of one programmed permutation -/

/-- Programming `permutation` at `label` to `range`. -/
def programmed (permutation : Equiv Block Block) (label range : Block) : Equiv Block Block :=
  permutation.trans (Equiv.swap (permutation label) range)

theorem programAt_fst (label : Block) (pair : Equiv Block Block × Block) :
    (programAt label pair).1 = programmed pair.1 label pair.2 := rfl

theorem programIndices_eq_programmed (programs : Programs)
    (oracle : PermutationOracle FixedKeyIndex Block) (index : FixedKeyIndex)
    (label range : Block) (requested : programs index = some (label, range)) :
    (programIndices programs oracle).permutation index =
      programmed (oracle.permutation index) label range :=
  programIndices_some programs oracle index label range requested

/-- The label values for which a forward query differs between a permutation and its
programming at that label to `value ^^^ label`. -/
def forwardHidden (permutation : Equiv Block Block) (value input : Block) : Finset Block :=
  {input, permutation input ^^^ value}

/-- The label values for which an inverse query differs. -/
def inverseHidden (permutation : Equiv Block Block) (value output : Block) : Finset Block :=
  {output ^^^ value, permutation.symm output}

theorem forwardHidden_card (permutation : Equiv Block Block) (value input : Block) :
    (forwardHidden permutation value input).card ≤ 2 :=
  Finset.card_le_two

theorem inverseHidden_card (permutation : Equiv Block Block) (value output : Block) :
    (inverseHidden permutation value output).card ≤ 2 :=
  Finset.card_le_two

/-- Off the two hidden label values, the programmed permutation answers a forward query
as the original. -/
theorem programmed_apply_of_not_mem (permutation : Equiv Block Block) (label value input : Block)
    (hidden : label ∉ forwardHidden permutation value input) :
    programmed permutation label (value ^^^ label) input = permutation input := by
  simp only [forwardHidden, Finset.mem_insert, Finset.mem_singleton, not_or] at hidden
  unfold programmed
  rw [Equiv.trans_apply]
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · intro equal
    exact hidden.1 (permutation.injective equal).symm
  · intro equal
    apply hidden.2
    rw [equal, BitVec.xor_comm value label, xor_xor_cancel]

/-- Off the two hidden label values, the programmed permutation answers an inverse query
as the original. -/
theorem programmed_symm_apply_of_not_mem (permutation : Equiv Block Block)
    (label value output : Block) (hidden : label ∉ inverseHidden permutation value output) :
    (programmed permutation label (value ^^^ label)).symm output = permutation.symm output := by
  simp only [inverseHidden, Finset.mem_insert, Finset.mem_singleton, not_or] at hidden
  unfold programmed
  rw [Equiv.symm_trans_apply, Equiv.symm_swap]
  congr 1
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · intro equal
    exact hidden.2 (by rw [equal, Equiv.symm_apply_apply])
  · intro equal
    apply hidden.1
    rw [equal, BitVec.xor_comm value label, xor_xor_cancel]

/-- The hidden label values of one query at one index, for programming that index at its
label to `value ^^^ label`. Queries at other indices and non-permutation queries hide nothing. -/
def hiddenLabels (oracle : PermutationOracle FixedKeyIndex Block) (index : FixedKeyIndex)
    (value : Block) : Query → Finset Block
  | .fixedForward index' input =>
    if index' = index then forwardHidden (oracle.permutation index) value input else ∅
  | .fixedInverse index' output =>
    if index' = index then inverseHidden (oracle.permutation index) value output else ∅
  | _ => ∅

theorem hiddenLabels_card (oracle : PermutationOracle FixedKeyIndex Block) (index : FixedKeyIndex)
    (value : Block) (query : Query) : (hiddenLabels oracle index value query).card ≤ 2 := by
  cases query with
  | fixedForward index' input =>
    simp only [hiddenLabels]
    split
    · exact forwardHidden_card _ _ _
    · simp
  | fixedInverse index' output =>
    simp only [hiddenLabels]
    split
    · exact inverseHidden_card _ _ _
    · simp
  | encForward _ _ => simp [hiddenLabels]
  | encInverse _ _ => simp [hiddenLabels]
  | hash _ => simp [hiddenLabels]

/-- Two views that differ only by programming one index at one label answer every query
whose hidden label values avoid that label identically. -/
theorem publicAnswer_programIndices_single (programs : Programs)
    (oracle : PermutationOracle FixedKeyIndex Block) (rest : PermutationOracle Garbling.EncIndex Block ×
      (BaseField → Block × Block)) (index : FixedKeyIndex) (label value : Block)
    (requested : programs index = some (label, value ^^^ label))
    (others : ∀ index', index' ≠ index → programs index' = none)
    (query : Query) (good : label ∉ hiddenLabels oracle index value query) :
    publicAnswer (programIndices programs oracle, rest) query = publicAnswer (oracle, rest) query := by
  cases query with
  | fixedForward index' input =>
    simp only [publicAnswer]
    by_cases same : index' = index
    · subst same
      rw [programIndices_eq_programmed programs oracle index' label _ requested]
      simp only [hiddenLabels] at good
      exact programmed_apply_of_not_mem _ _ _ _ good
    · rw [programIndices_none programs oracle index' (others index' same)]
  | fixedInverse index' output =>
    simp only [publicAnswer]
    by_cases same : index' = index
    · subst same
      rw [programIndices_eq_programmed programs oracle index' label _ requested]
      simp only [hiddenLabels] at good
      exact programmed_symm_apply_of_not_mem _ _ _ _ good
    · rw [programIndices_none programs oracle index' (others index' same)]
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash _ => rfl

end

end Kriterion.ArgoMAC.Security
