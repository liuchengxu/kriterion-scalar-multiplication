/-
This file proves perfect correctness of the scheme. On-curve labels release
exactly `bridgeKey`, and dividing the carrier by it returns the scalar.
-/

import Construction
import Security.Correctness

namespace Kriterion.ArgoMAC

open BN254

namespace Garbling

/-- The scalar modulus is below the base modulus, so a scalar's value is an
unreduced base-field value. -/
theorem val_scalarCast (scalar : ScalarField) :
    ((scalar.val : BaseField)).val = scalar.val := by
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (lt_trans scalar.val_lt (by decide))

/-- The carrier bits hold the exact field product. -/
theorem maskScalar_toNat (bridgeKey : NonZeroBase) (scalar : NonZeroScalar) :
    (maskScalar bridgeKey scalar).toNat =
      (bridgeKey.value * (scalar.value.val : BaseField)).val := by
  rw [maskScalar, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans (ZMod.val_lt _) (by decide))

/-- Dividing the mask by the bridge key returns the scalar. -/
theorem unmaskScalar_maskScalar [FieldCertificate] (bridgeKey : NonZeroBase)
    (scalar : NonZeroScalar) :
    unmaskScalar bridgeKey.value (maskScalar bridgeKey scalar) = scalar.value := by
  rw [unmaskScalar, maskScalar_toNat, ZMod.natCast_zmod_val, mul_right_comm,
    mul_inv_cancel₀ bridgeKey.nonzero, one_mul, val_scalarCast, ZMod.natCast_zmod_val]

/-- The circuit function equals the required scalar multiplication function. -/
theorem functionCorrect [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (input : AffineInput) :
    garbledCircuit.function scalar input = checkedScalarMultiplication scalar.value input :=
  rfl

/-- Every tape and every input evaluate to the checked scalar multiplication. -/
theorem perfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness garbledCircuit evaluationOracle := by
  intro parameter scalar tape input
  simp only [garbledCircuit, garble, encode, evaluate, evaluationOracle,
    Lamport.splitLabels_selectedLabels, checkedScalarMultiplication]
  cases decoded : decodePoint input with
  | none => rfl
  | some point =>
    have onCurve : OnCurve input :=
      (decodePoint_defined input).mp (by rw [decoded]; exact Option.some_ne_none point)
    simp only [CurveMembership.evaluateEncodedOnCurve _ _ _ _ _ _ _ onCurve,
      if_neg tape.bridgeKey.nonzero, unmaskScalar_maskScalar, Option.map_some,
      scalarMultiplication]

end Garbling
end Kriterion.ArgoMAC
