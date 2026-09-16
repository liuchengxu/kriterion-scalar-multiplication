/-
This file encodes the public value into bytes and proves the exact ciphertext
byte count. The curve-table encodings and their length lemmas reuse the
baseline wire format.
-/

import Construction.ArgoMAC.Public
import Encoding

namespace Kriterion.ArgoMAC

open BN254

namespace Wire

private def field : Encoding BaseField :=
  (Encoding.natural 32).map
    (fun value => ⟨value.val, lt_trans value.val_lt (by decide)⟩)
    (fun value => value.val)
    (fun value => ZMod.natCast_zmod_val value)

private def adaptor : Encoding BitAdaptor.Table :=
  (Encoding.natural 32).map
    (fun value => ⟨value.trueRow.toNat, value.trueRow.isLt⟩)
    (fun value => ⟨BitVec.ofNat 256 value.val⟩)
    (fun value => by cases value; simp)

private def digit := adaptor.vector coordinateBitCount

private def curve : Encoding CurveMembership.Table :=
  (field.pair (field.pair (field.pair
    (digit.pair (digit.pair (digit.pair (digit.pair digit))))))).map
    (fun value => (value.c0, value.c1, value.c2,
      value.x3, value.x5, value.x7, value.y4, value.y6))
    (fun ⟨c0, c1, c2, x3, x5, x7, y4, y6⟩ => ⟨c0, c1, c2, x3, x5, x7, y4, y6⟩)
    (fun _ => rfl)

/-- The 32-byte carrier encodes as its little-endian bytes. -/
private def carrier : Encoding (BitVec 256) :=
  (Encoding.natural 32).map
    (fun value => ⟨value.toNat, value.isLt⟩)
    (fun value => BitVec.ofNat 256 value.val)
    (fun value => by simp)

/-- This encoding includes the curve table and the carrier. -/
def encoding : Encoding Garbling.Public :=
  curve.pair carrier

@[simp] private theorem field_length (value : BaseField) :
    (field.encode value).length = 32 := by simp [field, Encoding.map]

@[simp] private theorem adaptor_length (value : BitAdaptor.Table) :
    (adaptor.encode value).length = 32 := by simp [adaptor, Encoding.map]

@[simp] private theorem digit_length (value : Vector BitAdaptor.Table coordinateBitCount) :
    (digit.encode value).length = 8128 :=
  Encoding.vector_length adaptor 32 coordinateBitCount value (fun _ => adaptor_length _)

@[simp] private theorem curve_length (value : CurveMembership.Table) :
    (curve.encode value).length = 40736 := by
  simp [curve, Encoding.map, Encoding.pair]

@[simp] private theorem carrier_length (value : BitVec 256) :
    (carrier.encode value).length = 32 := by simp [carrier, Encoding.map]

/-- Every public value encodes to exactly 40768 bytes. -/
theorem encoding_length (value : Garbling.Public) :
    (encoding.encode value).length = 40768 := by
  simp [encoding, Encoding.pair]

/-- The ciphertext byte count: every parameter, every nonzero scalar, and every
random tape produce exactly 40768 public bytes. -/
theorem garble_encode_length (parameter : Nat) (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) :
    (encoding.encode (Garbling.garble parameter scalar randomness).1).length = 40768 :=
  encoding_length _

end Wire
end Kriterion.ArgoMAC
