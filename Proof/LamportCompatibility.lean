/-
This file proves that the scheme's encoded labels are exactly the Lamport
selection of a 508-pair key at the challenge's input bits.

`affineLamportBits` is the 254 little-endian bits of `x` followed by the 254
little-endian bits of `y`, so the 508 pairs are the tape's per-bit label pairs
in the same order: the x key first, the y key second. The encoding
`Lamport.selectedLabels (key.randomness.inputMacKey.encodeAffine input)` packs
the selected labels in that order, so the two agree index by index.

The pairs are a computable function of the encoding key, so this file carries
data: the entry bundle must stay computable.
-/

import Construction
import Solution

namespace Kriterion.ArgoMAC.Lamport

open BN254 Cryptography

/-- The 508 Lamport pairs of one label key: the x pairs then the y pairs. -/
def keyPairs (key : InputMacKey) : GarbledCircuit.LamportSecretKey :=
  Vector.ofFn fun index =>
    if low : index.val < 254 then
      let item := key.x.get ⟨index.val, low⟩
      (item.falseLabel, item.trueLabel)
    else
      let item := key.y.get ⟨index.val - 254, by
        change index.val - 254 < 254
        omega⟩
      (item.falseLabel, item.trueLabel)

/-- The challenge's 508 input bits are the y bits above the x bits. -/
theorem affineLamportBits_eq_append (input : AffineInput) :
    affineLamportBits input = coordinateBits input.y ++ coordinateBits input.x := by
  apply BitVec.eq_of_toNat_eq
  simp only [affineLamportBits, BitVec.toNat_ofNat, BitVec.toNat_append,
    coordinateBitsToNat]
  rw [Nat.mod_eq_of_lt]
  · change input.x.val + input.y.val * 2 ^ 254 =
      input.y.val <<< 254 ||| input.x.val
    calc
      input.x.val + input.y.val * 2 ^ 254 =
          input.y.val <<< 254 + input.x.val := by
        rw [Nat.shiftLeft_eq]
        omega
      _ = input.y.val <<< 254 ||| input.x.val :=
        Nat.shiftLeft_add_eq_or_of_lt (lt_trans input.x.val_lt (by decide)) _
  · have xBound : input.x.val < 2 ^ 254 := lt_trans input.x.val_lt (by decide)
    have yBound : input.y.val < 2 ^ 254 := lt_trans input.y.val_lt (by decide)
    omega

private theorem appendGetLow (highBits lowBits : BitVec 254) (index : Nat)
    (bound : index < 508) (low : index < 254) :
    (highBits ++ lowBits).getLsb ⟨index, bound⟩ =
      lowBits.getLsb ⟨index, low⟩ := by
  change (highBits ++ lowBits).getLsbD index = lowBits.getLsbD index
  rw [BitVec.getLsbD_append, if_pos low]

private theorem appendGetHigh (highBits lowBits : BitVec 254) (index : Nat)
    (bound : index < 508) (high : 254 ≤ index) :
    (highBits ++ lowBits).getLsb ⟨index, bound⟩ =
      highBits.getLsb ⟨index - 254, by omega⟩ := by
  change (highBits ++ lowBits).getLsbD index = highBits.getLsbD (index - 254)
  rw [BitVec.getLsbD_append, if_neg (Nat.not_lt.mpr high)]

private theorem keyPairsGetLow (key : InputMacKey) (index : Nat)
    (bound : index < 508) (low : index < 254) :
    (keyPairs key)[index] =
      ((key.x.get ⟨index, low⟩).falseLabel, (key.x.get ⟨index, low⟩).trueLabel) := by
  unfold keyPairs
  rw [Vector.getElem_ofFn bound, dif_pos low]

private theorem keyPairsGetHigh (key : InputMacKey) (index : Nat)
    (bound : index < 508) (high : 254 ≤ index) :
    (keyPairs key)[index] =
      ((key.y.get ⟨index - 254, by
        change index - 254 < 254
        omega⟩).falseLabel,
      (key.y.get ⟨index - 254, by
        change index - 254 < 254
        omega⟩).trueLabel) := by
  unfold keyPairs
  rw [Vector.getElem_ofFn bound, dif_neg (Nat.not_lt.mpr high)]

private theorem selectedLabelsEncodeLow (key : InputMacKey) (input : AffineInput)
    (index : Nat) (bound : index < 508) (low : index < 254) :
    (selectedLabels (key.encodeAffine input))[index] =
      BitAdaptor.encode (key.x.get ⟨index, low⟩)
        ((coordinateBits input.x).getLsb ⟨index, low⟩) := by
  unfold selectedLabels InputMacKey.encodeAffine InputMacKey.encode
  rw [Vector.getElem_ofFn bound, dif_pos low]
  unfold encodeCoordinate
  change (Vector.ofFn fun coordinateIndex =>
    BitAdaptor.encode (key.x.get coordinateIndex)
      ((BitInput.ofAffine input).xBits.getLsb coordinateIndex))[index] = _
  simp only [Vector.getElem_ofFn]
  rfl

private theorem selectedLabelsEncodeHigh (key : InputMacKey) (input : AffineInput)
    (index : Nat) (bound : index < 508) (high : 254 ≤ index) :
    (selectedLabels (key.encodeAffine input))[index] =
      BitAdaptor.encode (key.y.get ⟨index - 254, by
        change index - 254 < 254
        omega⟩)
        ((coordinateBits input.y).getLsb ⟨index - 254, by
          change index - 254 < 254
          omega⟩) := by
  unfold selectedLabels InputMacKey.encodeAffine InputMacKey.encode
  rw [Vector.getElem_ofFn bound, dif_neg (Nat.not_lt.mpr high)]
  unfold encodeCoordinate
  have yBound : index - 254 < coordinateBitCount := by
    change index - 254 < 254
    omega
  change (Vector.ofFn fun coordinateIndex =>
    BitAdaptor.encode (key.y.get coordinateIndex)
      ((BitInput.ofAffine input).yBits.getLsb coordinateIndex))[index - 254] = _
  simp only [Vector.getElem_ofFn]
  rfl

/-- The packed labels are the Lamport selection at the challenge's input bits. -/
theorem selectedLabels_eq (key : InputMacKey) (input : AffineInput) :
    selectedLabels (key.encodeAffine input) =
      GarbledCircuit.selectLamportLabels (keyPairs key) (affineLamportBits input) := by
  rw [affineLamportBits_eq_append]
  apply Vector.ext
  intro index bound
  by_cases low : index < 254
  · have bitEq := appendGetLow (coordinateBits input.y) (coordinateBits input.x)
      index bound low
    rw [selectedLabelsEncodeLow key input index bound low]
    unfold GarbledCircuit.selectLamportLabels; rw [Vector.getElem_ofFn]
    change BitAdaptor.encode (key.x.get ⟨index, low⟩)
        ((coordinateBits input.x).getLsb ⟨index, low⟩) =
      if (coordinateBits input.y ++ coordinateBits input.x).getLsb ⟨index, bound⟩
      then (keyPairs key)[index].2 else (keyPairs key)[index].1
    rw [bitEq]
    rw [keyPairsGetLow key index bound low]
    rfl
  · have high : 254 ≤ index := Nat.le_of_not_gt low
    have bitEq := appendGetHigh (coordinateBits input.y) (coordinateBits input.x)
      index bound high
    rw [selectedLabelsEncodeHigh key input index bound high]
    unfold GarbledCircuit.selectLamportLabels; rw [Vector.getElem_ofFn]
    change BitAdaptor.encode (key.y.get ⟨index - 254, by
          change index - 254 < 254
          omega⟩)
        ((coordinateBits input.y).getLsb ⟨index - 254, by
          change index - 254 < 254
          omega⟩) =
      if (coordinateBits input.y ++ coordinateBits input.x).getLsb ⟨index, bound⟩
      then (keyPairs key)[index].2 else (keyPairs key)[index].1
    rw [bitEq]
    rw [keyPairsGetHigh key index bound high]
    rfl

/-- The scheme's encoding selects the required Lamport key branches. -/
theorem encodeSelectsLabels [FieldCertificate] [GroupCertificate]
    (key : Garbling.EncodingKey) (input : AffineInput) :
    Garbling.garbledCircuit.encode key input =
      GarbledCircuit.selectLamportLabels (keyPairs key.randomness.inputMacKey)
        (affineLamportBits input) :=
  selectedLabels_eq key.randomness.inputMacKey input

/-- The encoding key is a Lamport key for the challenge's 508 input bits. -/
def compatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility Garbling.garbledCircuit affineLamportBits where
  keyPairs key := keyPairs key.randomness.inputMacKey
  encodeSelectsLabels := encodeSelectsLabels

end Kriterion.ArgoMAC.Lamport
