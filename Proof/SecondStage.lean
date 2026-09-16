/-
This file proves the second-stage half of the independence bad-bound. The
first-stage bound defers the whole label key past a run that never reads it;
the second stage does read the key -- it runs on the selected labels -- but it
never reads the *other* label of any gate. So the unread labels, one per
coordinate and bit position, are deferred instead: replacing all of them at
once is an involution of the key, and after the deferral each log entry hits
the hidden set of its own gate's unread label with the mass of that set. The
union bound then costs one label set per log entry, not one per gate.
-/

import Proof.Product

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-! ### One label per coordinate and position -/

/-- One label slot of the key: a coordinate (`false` for `x`, `true` for `y`) and a bit
position. Which of the two labels is meant is fixed separately. -/
abbrev LabelIndex := Bool × Fin coordinateBitCount

/-- Replace one label of every position of a coordinate key. -/
def setCoordinateLabels (key : CoordinateMacKey) (values : Fin coordinateBitCount → Bool)
    (labels : Fin coordinateBitCount → Block) : CoordinateMacKey :=
  Vector.ofFn fun position => setPairLabel (key.get position) (values position) (labels position)

theorem get_setCoordinateLabels (key : CoordinateMacKey)
    (values : Fin coordinateBitCount → Bool) (labels : Fin coordinateBitCount → Block)
    (position : Fin coordinateBitCount) :
    (setCoordinateLabels key values labels).get position =
      setPairLabel (key.get position) (values position) (labels position) := by
  unfold setCoordinateLabels
  rw [Vector.get_eq_getElem, Vector.getElem_ofFn]

theorem setCoordinateLabels_get (key : CoordinateMacKey)
    (values : Fin coordinateBitCount → Bool) :
    setCoordinateLabels key values
        (fun position => BitAdaptor.encode (key.get position) (values position)) = key := by
  refine Vector.ext fun position member => ?_
  rw [← Vector.get_eq_getElem (index := ⟨position, member⟩),
    ← Vector.get_eq_getElem (index := ⟨position, member⟩), get_setCoordinateLabels,
    setPairLabel_encode]

theorem setCoordinateLabels_setCoordinateLabels (key : CoordinateMacKey)
    (values : Fin coordinateBitCount → Bool) (first second : Fin coordinateBitCount → Block) :
    setCoordinateLabels (setCoordinateLabels key values first) values second =
      setCoordinateLabels key values second := by
  refine Vector.ext fun position member => ?_
  rw [← Vector.get_eq_getElem (index := ⟨position, member⟩),
    ← Vector.get_eq_getElem (index := ⟨position, member⟩), get_setCoordinateLabels,
    get_setCoordinateLabels, get_setCoordinateLabels, setPairLabel_setPairLabel]

/-- Replace one label of every gate of the key. -/
def setKeyLabels (key : InputMacKey) (values : LabelIndex → Bool)
    (labels : LabelIndex → Block) : InputMacKey where
  x := setCoordinateLabels key.x (fun position => values (false, position))
    fun position => labels (false, position)
  y := setCoordinateLabels key.y (fun position => values (true, position))
    fun position => labels (true, position)

/-- The replaced labels of the key. -/
def keyLabels (key : InputMacKey) (values : LabelIndex → Bool) : LabelIndex → Block :=
  fun index => keyLabel key index.1 index.2 (values index)

theorem coordinateKey_setKeyLabels (key : InputMacKey) (values : LabelIndex → Bool)
    (labels : LabelIndex → Block) (coordinate : Bool) :
    coordinateKey (setKeyLabels key values labels) coordinate =
      setCoordinateLabels (coordinateKey key coordinate)
        (fun position => values (coordinate, position))
        fun position => labels (coordinate, position) := by
  cases coordinate <;> rfl

theorem keyLabels_setKeyLabels (key : InputMacKey) (values : LabelIndex → Bool)
    (labels : LabelIndex → Block) :
    keyLabels (setKeyLabels key values labels) values = labels := by
  funext index
  obtain ⟨coordinate, position⟩ := index
  unfold keyLabels keyLabel
  rw [coordinateKey_setKeyLabels, get_setCoordinateLabels, encode_setPairLabel]

theorem setKeyLabels_keyLabels (key : InputMacKey) (values : LabelIndex → Bool) :
    setKeyLabels key values (keyLabels key values) = key := by
  have coordinate : ∀ side : Bool,
      setCoordinateLabels (coordinateKey key side) (fun position => values (side, position))
        (fun position => keyLabels key values (side, position)) = coordinateKey key side := by
    intro side
    exact setCoordinateLabels_get (coordinateKey key side) fun position => values (side, position)
  obtain ⟨x, y⟩ := key
  exact congrArg₂ InputMacKey.mk (coordinate false) (coordinate true)

theorem setKeyLabels_setKeyLabels (key : InputMacKey) (values : LabelIndex → Bool)
    (first second : LabelIndex → Block) :
    setKeyLabels (setKeyLabels key values first) values second = setKeyLabels key values second := by
  unfold setKeyLabels
  simp only [setCoordinateLabels_setCoordinateLabels]

/-- Exchanging the replaced labels of the key with a separate family is an involution. -/
def swapKeyLabels (values : LabelIndex → Bool) :
    InputMacKey × (LabelIndex → Block) ≃ InputMacKey × (LabelIndex → Block) where
  toFun pair := (setKeyLabels pair.1 values pair.2, keyLabels pair.1 values)
  invFun pair := (setKeyLabels pair.1 values pair.2, keyLabels pair.1 values)
  left_inv pair := by
    obtain ⟨key, labels⟩ := pair
    simp only [Prod.mk.injEq]
    exact ⟨by rw [setKeyLabels_setKeyLabels, setKeyLabels_keyLabels],
      keyLabels_setKeyLabels key values labels⟩
  right_inv pair := by
    obtain ⟨key, labels⟩ := pair
    simp only [Prod.mk.injEq]
    exact ⟨by rw [setKeyLabels_setKeyLabels, setKeyLabels_keyLabels],
      keyLabels_setKeyLabels key values labels⟩

/-- A uniform key with one label of every gate replaced by a fresh uniform family is a
uniform key. -/
theorem uniform_bind_setKeyLabels {Outcome : Type} (values : LabelIndex → Bool)
    (continuation : InputMacKey → PMF Outcome) :
    ((PMF.uniformOfFintype InputMacKey).bind fun key =>
        (PMF.uniformOfFintype (LabelIndex → Block)).bind fun labels =>
          continuation (setKeyLabels key values labels)) =
      (PMF.uniformOfFintype InputMacKey).bind continuation := by
  rw [uniformOfFintype_bind_prod]
  have swapped := uniformOfFintype_bind_equiv (swapKeyLabels values)
    fun pair : InputMacKey × (LabelIndex → Block) => continuation pair.1
  simp only [swapKeyLabels, Equiv.coe_fn_mk] at swapped
  have unprod : ((PMF.uniformOfFintype (InputMacKey × (LabelIndex → Block))).bind fun pair =>
      continuation pair.1) =
      (PMF.uniformOfFintype InputMacKey).bind fun key =>
        (PMF.uniformOfFintype (LabelIndex → Block)).bind fun _ => continuation key :=
    (uniformOfFintype_bind_prod fun key (_ : LabelIndex → Block) => continuation key).symm
  rw [swapped, unprod]
  simp only [PMF.bind_const]

/-! ### One label of a uniform family is a uniform block -/

/-- Resampling one label of a uniform family is a uniform family. -/
theorem uniform_bind_update_labels (index : LabelIndex) :
    ((PMF.uniformOfFintype (LabelIndex → Block)).bind fun labels =>
        (PMF.uniformOfFintype Block).map fun block => Function.update labels index block) =
      PMF.uniformOfFintype (LabelIndex → Block) := by
  rw [uniformOfFintype_pi, productPMF_bind_update]
  refine congrArg productPMF (funext fun other => ?_)
  by_cases same : other = index
  · rw [same, Function.update_self]
  · rw [Function.update_of_ne same]

/-- One label of a uniform family is a uniform block. -/
theorem map_labels_uniform (index : LabelIndex) :
    (PMF.uniformOfFintype (LabelIndex → Block)).map (fun labels => labels index) =
      PMF.uniformOfFintype Block := by
  conv_lhs => rw [← uniform_bind_update_labels index]
  rw [PMF.map_bind]
  have inner : ∀ labels : LabelIndex → Block,
      ((PMF.uniformOfFintype Block).map fun block => Function.update labels index block).map
          (fun labels => labels index) = PMF.uniformOfFintype Block := by
    intro labels
    rw [PMF.map_comp]
    have identity : ((fun labels : LabelIndex → Block => labels index) ∘
        fun block => Function.update labels index block) = id :=
      funext fun block => by simp
    rw [identity, PMF.map_id]
  simp only [inner, PMF.bind_const]

/-- One label of a uniform family lies in a finite set of blocks with the mass of that
set. -/
theorem uniform_labels_mem (index : LabelIndex) (points : Finset Block) :
    (PMF.uniformOfFintype (LabelIndex → Block)).toOuterMeasure
        {labels | labels index ∈ points} = points.card / 2 ^ 128 := by
  have preimage : {labels : LabelIndex → Block | labels index ∈ points} =
      (fun labels : LabelIndex → Block => labels index) ⁻¹' (points : Set Block) := rfl
  rw [preimage, ← PMF.toOuterMeasure_map_apply, map_labels_uniform, uniform_block_toOuterMeasure]

/-! ### The second-stage bad bound -/

/-- The second-stage bad bound. A game that samples the label key up front and never reads
the labels selected by `values` hits, with any log entry, a label set determined by the
entry's own gate with mass at most the set size times the log budget over `2 ^ 128`. The
union bound runs over the log entries, not over the gates: the unread labels are deferred
as one family and each entry reads one coordinate of it. -/
theorem secondStage_hidden_le {Outcome Entry : Type} (game : InputMacKey → PMF Outcome)
    (values : LabelIndex → Bool)
    (unread : ∀ key labels, game (setKeyLabels key values labels) = game key)
    (log : Outcome → List Entry) (budget : Nat)
    (lengthLe : ∀ key, ∀ outcome ∈ (game key).support, (log outcome).length ≤ budget)
    (which : Entry → Option LabelIndex) (hidden : Outcome → Entry → Finset Block) (points : Nat)
    (cardLe : ∀ outcome entry, (hidden outcome entry).card ≤ points) :
    ((PMF.uniformOfFintype InputMacKey).bind fun key =>
        (game key).map fun outcome => (key, outcome)).toOuterMeasure
      {pair | ∃ entry ∈ log pair.2, ∃ index, which entry = some index ∧
        keyLabel pair.1 index.1 index.2 (values index) ∈ hidden pair.2 entry} ≤
      points * budget / 2 ^ 128 := by
  have deferred : ((PMF.uniformOfFintype InputMacKey).bind fun key =>
      (game key).map fun outcome => (key, outcome)) =
      (((PMF.uniformOfFintype InputMacKey).bind fun key => (game key).bind fun outcome =>
          (PMF.uniformOfFintype (LabelIndex → Block)).map fun labels => (key, outcome, labels)).map
        fun triple => (setKeyLabels triple.1 values triple.2.2, triple.2.1)) := by
    have right : (((PMF.uniformOfFintype InputMacKey).bind fun key => (game key).bind fun outcome =>
          (PMF.uniformOfFintype (LabelIndex → Block)).map fun labels => (key, outcome, labels)).map
        fun triple => (setKeyLabels triple.1 values triple.2.2, triple.2.1)) =
        (PMF.uniformOfFintype InputMacKey).bind fun key => (game key).bind fun outcome =>
          (PMF.uniformOfFintype (LabelIndex → Block)).map fun labels =>
            (setKeyLabels key values labels, outcome) := by
      rw [PMF.map_bind]
      refine congrArg (PMF.bind (PMF.uniformOfFintype InputMacKey)) (funext fun key => ?_)
      rw [PMF.map_bind]
      refine congrArg (PMF.bind (game key)) (funext fun outcome => ?_)
      rw [PMF.map_comp]
      rfl
    have left : ((PMF.uniformOfFintype InputMacKey).bind fun key =>
        (game key).map fun outcome => (key, outcome)) =
        (PMF.uniformOfFintype InputMacKey).bind fun key => (game key).bind fun outcome =>
          (PMF.uniformOfFintype (LabelIndex → Block)).map fun labels =>
            (setKeyLabels key values labels, outcome) := by
      rw [← uniform_bind_setKeyLabels values fun key =>
        (game key).map fun outcome => (key, outcome)]
      refine congrArg (PMF.bind (PMF.uniformOfFintype InputMacKey)) (funext fun key => ?_)
      have replaced : ∀ labels : LabelIndex → Block,
          (game (setKeyLabels key values labels)).map
              (fun outcome => (setKeyLabels key values labels, outcome)) =
            (game key).map fun outcome => (setKeyLabels key values labels, outcome) := by
        intro labels
        rw [unread key labels]
      simp only [replaced]
      exact PMF.bind_comm (PMF.uniformOfFintype (LabelIndex → Block)) (game key)
        fun labels outcome => PMF.pure (setKeyLabels key values labels, outcome)
    rw [left, right]
  rw [deferred, PMF.toOuterMeasure_map_apply]
  have event : ((fun triple : InputMacKey × Outcome × (LabelIndex → Block) =>
        (setKeyLabels triple.1 values triple.2.2, triple.2.1)) ⁻¹'
      {pair : InputMacKey × Outcome |
        ∃ entry ∈ log pair.2, ∃ index, which entry = some index ∧
          keyLabel pair.1 index.1 index.2 (values index) ∈ hidden pair.2 entry}) =
      {triple : InputMacKey × Outcome × (LabelIndex → Block) |
        ∃ entry ∈ log triple.2.1, triple.2.2 ∈
          {labels : LabelIndex → Block | ∃ index, which entry = some index ∧
            labels index ∈ hidden triple.2.1 entry}} := by
    ext triple
    obtain ⟨key, outcome, labels⟩ := triple
    have label : ∀ index : LabelIndex,
        keyLabel (setKeyLabels key values labels) index.1 index.2 (values index) = labels index :=
      fun index => congrFun (keyLabels_setKeyLabels key values labels) index
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, label]
  rw [event]
  refine le_trans (hidden_label_bound (PMF.uniformOfFintype InputMacKey) game
    (PMF.uniformOfFintype (LabelIndex → Block)) (fun _ outcome => log outcome)
    (fun _ outcome entry => {labels : LabelIndex → Block | ∃ index, which entry = some index ∧
      labels index ∈ hidden outcome entry})
    budget (points / 2 ^ 128) (fun key outcome member => lengthLe key outcome member) ?_) ?_
  · intro _ outcome entry
    rcases whichEntry : which entry with _ | index
    · simp only [reduceCtorEq, false_and, exists_false, Set.ofPred_false]
      rw [MeasureTheory.measure_empty]
      exact bot_le
    · have same : {labels : LabelIndex → Block |
          ∃ other, (some index : Option LabelIndex) = some other ∧
            labels other ∈ hidden outcome entry} =
          {labels : LabelIndex → Block | labels index ∈ hidden outcome entry} := by
        ext labels
        simp only [Option.some.injEq, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨_, rfl, member⟩
          exact member
        · intro member
          exact ⟨index, rfl, member⟩
      rw [same, uniform_labels_mem]
      exact ENNReal.div_le_div_right (Nat.cast_le.mpr (cardLe outcome entry)) _
  · exact le_of_eq (by rw [div_eq_mul_inv, div_eq_mul_inv]; ring)

end

end Kriterion.ArgoMAC.Security
