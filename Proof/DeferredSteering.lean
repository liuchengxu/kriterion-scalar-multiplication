/-
This file puts the second-stage steering in the form the reference game uses.

The reference game programs each gate's fixed-key permutations only at the
selected label: the hash slots of a `false` gate to a fiber sample of the gate's
selected output, the pad slots of a `true` gate to the table row masked with
that output. This file proves that the programmed view then releases exactly the
selected outputs, so that the curve evaluation on the honest labels releases
`bridgeKey + mask * curveGap input`, which on the curve is the bridge key
itself. The steering therefore asks for `selected output + (target - bridgeKey)`
at the steering gate: on the visible data it is the shift `shiftMiddle` of the
reference coordinates.

The file also proves the reparametrisation that turns the double programming of
the steering gate (honest, then steered) into the single programming of the
reference game: programming a permutation at one label twice is programming the
permutation composed with the swap of the two ranges once.
-/

import Proof.Hidden

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit

/-! ### Programming one label twice -/

/-- Composing the two transpositions of a double programming is the transposition of the
second range with the first image, applied after the swap of the two ranges. -/
theorem swap_trans_swap (image first second : Block) (freshFirst : image ≠ first)
    (freshSecond : image ≠ second) :
    (Equiv.swap image first).trans (Equiv.swap first second) =
      (Equiv.swap first second).trans (Equiv.swap image second) := by
  have imageFirst : first ≠ image := Ne.symm freshFirst
  have imageSecond : second ≠ image := Ne.symm freshSecond
  refine Equiv.ext fun value => ?_
  simp only [Equiv.trans_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/-- Programming a permutation at one label twice is programming the permutation composed
with the swap of the two ranges once. The steered permutation of the simulated game is
therefore the singly programmed permutation of the reference game, read on a
reparametrised unprogrammed permutation. -/
theorem programmed_programmed (permutation : Equiv Block Block) (label first second : Block)
    (freshFirst : permutation label ≠ first) (freshSecond : permutation label ≠ second) :
    programmed (programmed permutation label first) label second =
      programmed (permutation.trans (Equiv.swap first second)) label second := by
  have firstImage : programmed permutation label first label = first := by
    show (permutation.trans (Equiv.swap (permutation label) first)) label = first
    rw [Equiv.trans_apply, Equiv.swap_apply_left]
  have secondImage : (permutation.trans (Equiv.swap first second)) label = permutation label := by
    rw [Equiv.trans_apply]
    exact Equiv.swap_apply_of_ne_of_ne freshFirst freshSecond
  have left : programmed (programmed permutation label first) label second =
      (permutation.trans (Equiv.swap (permutation label) first)).trans
        (Equiv.swap first second) := by
    show (programmed permutation label first).trans
      (Equiv.swap ((programmed permutation label first) label) second) = _
    rw [firstImage]
    rfl
  have right : programmed (permutation.trans (Equiv.swap first second)) label second =
      (permutation.trans (Equiv.swap first second)).trans
        (Equiv.swap (permutation label) second) := by
    show (permutation.trans (Equiv.swap first second)).trans
      (Equiv.swap ((permutation.trans (Equiv.swap first second)) label) second) = _
    rw [secondImage]
  rw [left, right, Equiv.trans_assoc, Equiv.trans_assoc,
    swap_trans_swap (permutation label) first second freshFirst freshSecond]

/-! ### The gates of the programmed reference view -/

/-- The gate permutations of one adaptor at one coordinate bit position. -/
theorem fixedKeyPermutations_val (oracle : PermutationOracle FixedKeyIndex Block)
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount) :
    fixedKeyPermutations oracle adaptor position.val =
      { hash := fun slot => oracle.permutation ⟨adaptor, position, .hash slot⟩
        pad := fun slot => oracle.permutation ⟨adaptor, position, .pad slot⟩ } := by
  have same : (⟨position.val % coordinateBitCount, Nat.mod_lt _ (by decide)⟩ :
      Fin coordinateBitCount) = position :=
    Fin.ext (Nat.mod_eq_of_lt position.isLt)
  simp only [fixedKeyPermutations, same]

/-- At a `false` gate the programmed view hashes the selected label to the fiber sample. -/
theorem hashToField_programSelected (oracle : PermutationOracle FixedKeyIndex Block)
    (key : InputMacKey) (input : AffineInput) (outputs : GateValues BaseField)
    (rows : GateValues BitAdaptor.Ciphertext) (fibers : GateValues (BitVec 384))
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount)
    (bit : inputBits input adaptor position = false) :
    (fixedKeyGate (programIndices (selectedPrograms key input outputs rows fibers) oracle)
        adaptor position.val).hashToField (selectedLabel key input adaptor position) =
      (((fibers adaptor position).toNat : Nat) : BaseField) := by
  have slot : ∀ (chunk : Fin 3) (start : Nat), 128 * chunk.val = start →
      (programIndices (selectedPrograms key input outputs rows fibers) oracle).permutation
          ⟨adaptor, position, .hash chunk⟩ (selectedLabel key input adaptor position) =
        (fibers adaptor position).extractLsb' start 128 ^^^
          selectedLabel key input adaptor position := by
    intro chunk start offset
    refine programIndices_apply_label _ _ _ _ _ ?_
    rw [selectedPrograms_hash, bit, if_neg Bool.false_ne_true, slotRange, offset]
  simp only [fixedKeyGate, BitAdaptor.fixedKeyOracle, BitAdaptor.hashBytes,
    fixedKeyPermutations_val, daviesMeyer, Cryptography.xor]
  rw [slot 0 0 rfl, slot 1 128 rfl, slot 2 256 rfl, xor_xor_cancel, xor_xor_cancel,
    xor_xor_cancel, append_extract_384]

/-- At a `true` gate the programmed view pads the selected label with the row masked by the
selected output. -/
theorem padBytes_programSelected (oracle : PermutationOracle FixedKeyIndex Block)
    (key : InputMacKey) (input : AffineInput) (outputs : GateValues BaseField)
    (rows : GateValues BitAdaptor.Ciphertext) (fibers : GateValues (BitVec 384))
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount)
    (bit : inputBits input adaptor position = true) :
    BitAdaptor.padBytes
        (fixedKeyPermutations (programIndices (selectedPrograms key input outputs rows fibers)
          oracle) adaptor position.val) (selectedLabel key input adaptor position) =
      rows adaptor position ^^^ BitAdaptor.fieldBytes (outputs adaptor position) := by
  have slot : ∀ (chunk : Fin 2) (start : Nat), 128 * chunk.val = start →
      (programIndices (selectedPrograms key input outputs rows fibers) oracle).permutation
          ⟨adaptor, position, .pad chunk⟩ (selectedLabel key input adaptor position) =
        (rows adaptor position ^^^
            BitAdaptor.fieldBytes (outputs adaptor position)).extractLsb' start 128 ^^^
          selectedLabel key input adaptor position := by
    intro chunk start offset
    refine programIndices_apply_label _ _ _ _ _ ?_
    rw [selectedPrograms_pad, bit, if_pos rfl, slotRange, offset]
  simp only [BitAdaptor.padBytes, fixedKeyPermutations_val, daviesMeyer, Cryptography.xor]
  rw [slot 0 0 rfl, slot 1 128 rfl, xor_xor_cancel, xor_xor_cancel, append_extract_256]

/-- At a `true` gate the programmed view decrypts the row to the selected output. -/
theorem decrypt_programSelected (oracle : PermutationOracle FixedKeyIndex Block)
    (key : InputMacKey) (input : AffineInput) (outputs : GateValues BaseField)
    (rows : GateValues BitAdaptor.Ciphertext) (fibers : GateValues (BitVec 384))
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount)
    (bit : inputBits input adaptor position = true) :
    (fixedKeyGate (programIndices (selectedPrograms key input outputs rows fibers) oracle)
        adaptor position.val).decrypt (selectedLabel key input adaptor position)
        (rows adaptor position) =
      outputs adaptor position := by
  simp only [fixedKeyGate, BitAdaptor.fixedKeyOracle]
  rw [padBytes_programSelected oracle key input outputs rows fibers adaptor position bit,
    BitVec.xor_comm (rows adaptor position), BitVec.xor_assoc, BitVec.xor_self,
    BitVec.xor_zero]
  simp only [BitAdaptor.fieldBytes, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (lt_trans (outputs adaptor position).val_lt (by decide))]
  exact ZMod.natCast_zmod_val _

/-- Every gate of the programmed reference view releases its selected output. -/
theorem evaluate_programSelected (oracle : PermutationOracle FixedKeyIndex Block)
    (key : InputMacKey) (input : AffineInput) (outputs : GateValues BaseField)
    (rows : GateValues BitAdaptor.Ciphertext) (fibers : GateValues (BitVec 384))
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount)
    (fiberValue : (((fibers adaptor position).toNat : Nat) : BaseField) = outputs adaptor position)
    (table : BitAdaptor.Table) (row : table.trueRow = rows adaptor position) :
    BitAdaptor.evaluate
        (fixedKeyGate (programIndices (selectedPrograms key input outputs rows fibers) oracle)
          adaptor position.val) table (inputBits input adaptor position)
        (selectedLabel key input adaptor position) =
      outputs adaptor position := by
  unfold BitAdaptor.evaluate
  cases bit : inputBits input adaptor position with
  | false =>
    rw [if_neg Bool.false_ne_true]
    exact (hashToField_programSelected oracle key input outputs rows fibers adaptor position
      bit).trans fiberValue
  | true =>
    rw [if_pos rfl, row]
    exact decrypt_programSelected oracle key input outputs rows fibers adaptor position bit

/-! ### The curve evaluation of the programmed reference view -/

/-- The selected labels one adaptor family reads: the x labels for the x adaptors, the y
labels for the y adaptors. -/
def gateMac (mac : InputMac) : CurveAdaptor → CoordinateMac
  | .y4 | .y6 => mac.y
  | .x3 | .x5 | .x7 => mac.x

theorem gateMac_encodeAffine (key : InputMacKey) (input : AffineInput) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) :
    (gateMac (key.encodeAffine input) adaptor).get position =
      selectedLabel key input adaptor position := by
  cases adaptor <;>
    simp only [gateMac, InputMacKey.encodeAffine, InputMacKey.encode, BitInput.ofAffine,
      encodeCoordinate, selectedLabel, gateKey, inputBits, coordinateValues,
      Vector.get_eq_getElem, Vector.getElem_ofFn]

/-- Every adaptor family of the programmed reference view releases the field element its
selected outputs encode. -/
theorem evaluateDigit_programSelected (oracle : PermutationOracle FixedKeyIndex Block)
    (bridgeKey : BaseField) (key : InputMacKey) (raw : Coordinates) (input : AffineInput)
    (fibers : GateValues (BitVec 384))
    (fiberValues : ∀ adaptor position, (((fibers adaptor position).toNat : Nat) : BaseField) =
      (encodeCoordinates input raw).hash adaptor position)
    (adaptor : CurveAdaptor) (value : BaseField)
    (bits : inputBits input adaptor = coordinateValues value) :
    CurveMembership.evaluateDigit
        (fixedKeyGate (programIndices (selectedPrograms key input
          (encodeCoordinates input raw).hash (tableRow (raw.table bridgeKey key)) fibers) oracle)
          adaptor)
        (tableRows (raw.table bridgeKey key) adaptor) value
        (gateMac (key.encodeAffine input) adaptor) =
      DigitAdaptor.fromBits ((encodeCoordinates input raw).hash adaptor) := by
  unfold CurveMembership.evaluateDigit
  refine congrArg DigitAdaptor.fromBits ?_
  funext index
  rw [DigitAdaptor.evaluate, Vector.get_ofFn, ← bits, gateMac_encodeAffine]
  exact evaluate_programSelected oracle key input _ _ fibers adaptor index
    (fiberValues adaptor index) _ rfl

/-- The programmed reference view releases the membership polynomial of the reference
table: on the curve it releases the bridge key itself. -/
theorem curveEvaluate_programSelected (oracle : PermutationOracle FixedKeyIndex Block)
    (bridgeKey : BaseField) (key : InputMacKey) (raw : Coordinates) (input : AffineInput)
    (fibers : GateValues (BitVec 384))
    (fiberValues : ∀ adaptor position, (((fibers adaptor position).toNat : Nat) : BaseField) =
      (encodeCoordinates input raw).hash adaptor position) :
    CurveMembership.evaluate
        (curveOracles (programIndices (selectedPrograms key input
          (encodeCoordinates input raw).hash (tableRow (raw.table bridgeKey key)) fibers) oracle))
        (raw.table bridgeKey key) input (key.encodeAffine input) =
      bridgeKey + raw.mask * curveGap input := by
  set programmedOracle := programIndices (selectedPrograms key input
    (encodeCoordinates input raw).hash (tableRow (raw.table bridgeKey key)) fibers) oracle
    with programmedOracleDef
  have digit : ∀ (adaptor : CurveAdaptor) (value : BaseField),
      inputBits input adaptor = coordinateValues value →
      CurveMembership.evaluateDigit (fixedKeyGate programmedOracle adaptor)
          (tableRows (raw.table bridgeKey key) adaptor) value
          (gateMac (key.encodeAffine input) adaptor) =
        DigitAdaptor.fromBits ((encodeCoordinates input raw).hash adaptor) := by
    rw [programmedOracleDef]
    exact fun adaptor value bits => evaluateDigit_programSelected oracle bridgeKey key raw input
      fibers fiberValues adaptor value bits
  have x3 : CurveMembership.evaluateDigit (fixedKeyGate programmedOracle .x3)
      (raw.table bridgeKey key).x3 input.x (key.encodeAffine input).x =
      DigitAdaptor.fromBits ((encodeCoordinates input raw).hash .x3) := digit .x3 input.x rfl
  have y4 : CurveMembership.evaluateDigit (fixedKeyGate programmedOracle .y4)
      (raw.table bridgeKey key).y4 input.y (key.encodeAffine input).y =
      DigitAdaptor.fromBits ((encodeCoordinates input raw).hash .y4) := digit .y4 input.y rfl
  have x5 : CurveMembership.evaluateDigit (fixedKeyGate programmedOracle .x5)
      (raw.table bridgeKey key).x5 input.x (key.encodeAffine input).x =
      DigitAdaptor.fromBits ((encodeCoordinates input raw).hash .x5) := digit .x5 input.x rfl
  have y6 : CurveMembership.evaluateDigit (fixedKeyGate programmedOracle .y6)
      (raw.table bridgeKey key).y6 input.y (key.encodeAffine input).y =
      DigitAdaptor.fromBits ((encodeCoordinates input raw).hash .y6) := digit .y6 input.y rfl
  have x7 : CurveMembership.evaluateDigit (fixedKeyGate programmedOracle .x7)
      (raw.table bridgeKey key).x7 input.x (key.encodeAffine input).x =
      DigitAdaptor.fromBits ((encodeCoordinates input raw).hash .x7) := digit .x7 input.x rfl
  simp only [CurveMembership.evaluate, curveOracles]
  rw [x3, y4, x5, y6, x7, Coordinates.table_c0_eq bridgeKey key raw input,
    Coordinates.table_c1, Coordinates.table_c2]
  have r1 : (encodeCoordinates input raw).r1 = raw.mask + raw.r1 := rfl
  have r2 : (encodeCoordinates input raw).r2 = -raw.mask + raw.r2 := rfl
  unfold offsetTerm
  rw [r1, r2]
  ring

/-! ### The steering shift -/

/-- The steering gate reads the position-`0` bit of the x coordinate. -/
theorem steeringBit_eq (input : AffineInput) : steeringBit input = inputBits input .x7 0 := rfl

noncomputable section

/-- The steering of an explicit released value: what `steer` does once the value it must
release at the steering gate is known. -/
def steerTo (state : State) (input : AffineInput) (mac : InputMac) (wanted : BaseField) :
    PMF State :=
  if steeringBit input then
    PMF.pure (programAll state (padRequests (mac.x.get 0)
      (BitAdaptor.fieldBytes wanted ^^^ (state.table.x7.get 0).trueRow)))
  else
    (uniformHashFiber wanted).map fun hash =>
      programAll state (hashRequests (mac.x.get 0) hash)

theorem steer_eq_steerTo (state : State) (input : AffineInput) (mac : InputMac)
    (target : BaseField) :
    steer state input mac target =
      steerTo state input mac
        (BitAdaptor.evaluate (fixedKeyGate state.view.1 .x7 0) (state.table.x7.get 0)
            (steeringBit input) (mac.x.get 0) +
          (target - CurveMembership.evaluate (curveOracles state.view.1) state.table input mac)) :=
  rfl

/-- The steering shift at the steering gate. -/
theorem shiftSteering_steeringGate (shift : BaseField) (outputs : GateValues BaseField) :
    shiftSteering shift outputs .x7 0 = outputs .x7 0 + shift := by
  simp [shiftSteering]

/-- Steering in deferred form. On an on-curve input the reference view already releases the
bridge key, so the steering asks the steering gate for its selected output shifted by
`target - bridgeKey`: on the visible data the steering is exactly `shiftMiddle`. -/
theorem steer_programSelected (oracle : PermutationOracle FixedKeyIndex Block)
    (bridgeKey : BaseField) (key : InputMacKey) (raw : Coordinates) (input : AffineInput)
    (fibers : GateValues (BitVec 384)) (target : BaseField) (state : State)
    (view : state.view.1 = programIndices (selectedPrograms key input
      (encodeCoordinates input raw).hash (tableRow (raw.table bridgeKey key)) fibers) oracle)
    (table : state.table = raw.table bridgeKey key)
    (fiberValues : ∀ adaptor position, (((fibers adaptor position).toNat : Nat) : BaseField) =
      (encodeCoordinates input raw).hash adaptor position)
    (onCurve : curveGap input = 0) :
    steer state input (key.encodeAffine input) target =
      steerTo state input (key.encodeAffine input)
        ((shiftMiddle (target - bridgeKey) (encodeCoordinates input raw)).hash .x7 0) := by
  have released : CurveMembership.evaluate (curveOracles state.view.1) state.table input
      (key.encodeAffine input) = bridgeKey := by
    rw [view, table, curveEvaluate_programSelected oracle bridgeKey key raw input fibers
      fiberValues, onCurve, mul_zero, add_zero]
  have gate : BitAdaptor.evaluate (fixedKeyGate state.view.1 .x7 0) (state.table.x7.get 0)
      (steeringBit input) ((key.encodeAffine input).x.get 0) =
      (encodeCoordinates input raw).hash .x7 0 := by
    rw [view, table, steeringBit_eq,
      show ((key.encodeAffine input).x.get 0) =
        selectedLabel key input .x7 0 from gateMac_encodeAffine key input .x7 0]
    exact evaluate_programSelected oracle key input _ _ fibers .x7 0 (fiberValues .x7 0) _ rfl
  rw [steer_eq_steerTo, released, gate]
  exact congrArg (steerTo state input (key.encodeAffine input))
    (shiftSteering_steeringGate (target - bridgeKey) (encodeCoordinates input raw).hash).symm

end

end Kriterion.ArgoMAC.Security
