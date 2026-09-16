/-
This file defines the garbling scheme: label packing in Lamport order, the
evaluator, and the `GarbledCircuit` record. The evaluator recovers the input
labels by a plain split, runs the curve-membership table, and divides the
carrier by the released value.
-/

import Construction.ArgoMAC.Public
import GarbledCircuit
import ScalarMultiplication

namespace Kriterion.ArgoMAC

open BN254 Cryptography

namespace Lamport

/-- The 508 blocks store the 254 x labels before the 254 y labels. -/
def selectedLabels (mac : InputMac) : GarbledCircuit.LamportSignature :=
  Vector.ofFn fun index =>
    if low : index.val < 254 then
      mac.x.get ⟨index.val, low⟩
    else
      mac.y.get ⟨index.val - 254, by
        change index.val - 254 < 254
        omega⟩

/-- The evaluator reads the x labels from the first half and the y labels from
the second half. -/
def splitLabels (labels : GarbledCircuit.LamportSignature) : InputMac := {
  x := Vector.ofFn fun index => labels[index.val]'(by have : index.val < 254 := index.isLt; omega)
  y := Vector.ofFn fun index => labels[254 + index.val]'(by have : index.val < 254 := index.isLt; omega)
}

/-- The split restores exactly the packed labels. -/
theorem splitLabels_selectedLabels (mac : InputMac) :
    splitLabels (selectedLabels mac) = mac := by
  apply InputMac.ext
  · apply Vector.ext
    intro index bound
    simp only [splitLabels, selectedLabels, Vector.getElem_ofFn]
    rw [dif_pos (show index < 254 from bound)]
    rfl
  · apply Vector.ext
    intro index bound
    simp only [splitLabels, selectedLabels, Vector.getElem_ofFn]
    rw [dif_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl

end Lamport

namespace Garbling

/-- The encoding packs the selected per-bit MAC values in Lamport order. -/
def encode (key : EncodingKey) (input : AffineInput) : GarbledCircuit.LamportSignature :=
  Lamport.selectedLabels (key.randomness.inputMacKey.encodeAffine input)

/-- The evaluator divides the carrier by the released value and reads the
quotient as a scalar. -/
def unmaskScalar (released : BaseField) (carrier : BitVec 256) : ScalarField :=
  (((carrier.toNat : BaseField) * released⁻¹).val : ScalarField)

/-- The evaluation oracle is the tape's public triple. -/
def evaluationOracle (tape : Randomness) : PublicOracle FixedKeyIndex EncIndex :=
  (tape.fixedKeyOracle, tape.encOracle, tape.hashOracle)

/-- Off-curve inputs are rejected before any table read. On-curve inputs
release the bridge key, which unmasks the scalar. A zero release is an
evaluation failure; correct labels never produce it. -/
def evaluate [FieldCertificate] [GroupCertificate]
    (oracle : PublicOracle FixedKeyIndex EncIndex) (circuit : Public)
    (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    Option (Option Point) :=
  match decodePoint input with
  | none => some none
  | some point =>
    let released :=
      CurveMembership.evaluate (curveOracles oracle.1) circuit.1 input
        (Lamport.splitLabels labels)
    if released = 0 then none
    else some (some (unmaskScalar released circuit.2 • point))

/-- The scheme's target is the checked scalar multiplication. -/
def garbledCircuit [FieldCertificate] [GroupCertificate] :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      EncodingKey GarbledCircuit.LamportSignature (PublicOracle FixedKeyIndex EncIndex) := {
  function := fun scalar input => checkedScalarMultiplication scalar.value input
  garble
  encode
  evaluate
}

end Garbling
end Kriterion.ArgoMAC
