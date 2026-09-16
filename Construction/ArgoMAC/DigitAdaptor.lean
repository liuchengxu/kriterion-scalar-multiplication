/-
This file composes the per-bit tables of one coordinate.
-/

import Construction.ArgoMAC.BitAdaptor
import Batteries.Data.Vector.Lemmas

namespace Kriterion.ArgoMAC.DigitAdaptor

open BN254

def encode {count : Nat} (keys : Vector BitAdaptor.Key count)
    (values : Fin count → Bool) : Vector Cryptography.Block count :=
  Vector.ofFn fun index => BitAdaptor.encode (keys.get index) (values index)

def garble {count : Nat} (windows : Nat → BitAdaptor.FixedKeyOracle)
    (slope : BaseField) (keys : Vector BitAdaptor.Key count) :
    Vector BitAdaptor.Table count × Vector BitAdaptor.OutputKey count :=
  let garbled := Vector.ofFn fun index =>
    BitAdaptor.garble
      (windows index.val) slope (keys.get index)
  (garbled.map Prod.fst, garbled.map Prod.snd)

def evaluate {count : Nat} (windows : Nat → BitAdaptor.FixedKeyOracle)
    (values : Fin count → Bool) (tables : Vector BitAdaptor.Table count)
    (inputs : Vector Cryptography.Block count) : Vector BaseField count :=
  Vector.ofFn fun index =>
    BitAdaptor.evaluate (windows index.val)
      (tables.get index) (values index) (inputs.get index)

def selectedOutputs {count : Nat} (keys : Vector BitAdaptor.OutputKey count)
    (values : Fin count → Bool) : Vector BaseField count :=
  Vector.ofFn fun index => (keys.get index).encode (values index)

/-- This is the `pow_two_lincomb` operation. -/
def fromBits {count : Nat} (values : Fin count → BaseField) : BaseField :=
  Fin.foldr count (fun index value => 2 * value + values index) 0

def bitValue {count : Nat} (values : Fin count → Bool) : BaseField :=
  fromBits fun index => if values index then 1 else 0

/-- The algorithm calls this value `bits_k`. -/
def bitsK {count : Nat} (keys : Vector BitAdaptor.OutputKey count) : BaseField :=
  fromBits fun index => (keys.get index).offset

theorem fromBitsBool {count : Nat} (bits : Fin count → Bool) :
    bitValue bits = (Nat.ofBits bits : BaseField) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [bitValue, fromBits, Fin.foldr_succ, Nat.ofBits_succ]
      change 2 * bitValue (fun index => bits index.succ) +
          (if bits 0 then 1 else 0) = _
      have tail := inductionHypothesis (bits ∘ Fin.succ)
      change bitValue (fun index => bits index.succ) = _ at tail
      rw [tail]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      cases bits 0 <;> rfl

theorem bitValueGetLsb {count : Nat} (value : BitVec count) :
    bitValue value.getLsb = (value.toNat : BaseField) := by
  rw [fromBitsBool]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases inRange : index < count
  · simp [Nat.testBit_ofBits_lt _ index inRange, BitVec.getLsb]
  · have above : count ≤ index := Nat.le_of_not_gt inRange
    rw [Nat.testBit_ofBits_ge _ index above]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le value.toFin.isLt
      (Nat.pow_le_pow_right (by decide) above))).symm

theorem fromBitsAffine {count : Nat} (slope : BaseField)
    (offsets : Fin count → BaseField) (values : Fin count → Bool) :
    fromBits (fun index => if values index then slope + offsets index else offsets index) =
      slope * bitValue values + fromBits offsets := by
  induction count with
  | zero => simp [fromBits, bitValue]
  | succ count inductionHypothesis =>
      rw [fromBits, Fin.foldr_succ, bitValue, fromBits, Fin.foldr_succ,
        fromBits, Fin.foldr_succ]
      have tail := inductionHypothesis (offsets ∘ Fin.succ) (values ∘ Fin.succ)
      change Fin.foldr count (fun index value => 2 * value +
          if values index.succ then slope + offsets index.succ else offsets index.succ) 0 =
        slope * Fin.foldr count (fun index value => 2 * value +
          if values index.succ then 1 else 0) 0 +
        Fin.foldr count (fun index value => 2 * value + offsets index.succ) 0 at tail
      rw [tail]
      cases values 0 <;> simp <;> ring

theorem fromBitsSelectedOutputs {count : Nat} (slope : BaseField)
    (keys : Vector BitAdaptor.OutputKey count)
    (sameSlope : ∀ index : Fin count, (keys.get index).slope = slope)
    (values : Fin count → Bool) :
    fromBits (fun index => (selectedOutputs keys values).get index) =
      slope * bitValue values + bitsK keys := by
  have encoded : (fun index => (selectedOutputs keys values).get index) =
      (fun index => if values index then slope + (keys.get index).offset
        else (keys.get index).offset) := by
    funext index
    simp only [selectedOutputs, BitAdaptor.OutputKey.encode, Vector.get_ofFn]
    rw [sameSlope index]
  rw [encoded, fromBitsAffine]
  rfl

theorem evaluateGarbleEncode {count : Nat}
    (windows : Nat → BitAdaptor.FixedKeyOracle) (slope : BaseField)
    (keys : Vector BitAdaptor.Key count) (values : Fin count → Bool) :
    evaluate windows values (garble windows slope keys).1 (encode keys values) =
      selectedOutputs (garble windows slope keys).2 values := by
  apply Vector.ext
  intro index inRange
  simp [evaluate, garble, encode, selectedOutputs, BitAdaptor.evaluateEncode]

theorem garbleSlope {count : Nat} (windows : Nat → BitAdaptor.FixedKeyOracle)
    (slope : BaseField) (keys : Vector BitAdaptor.Key count) (index : Fin count) :
    ((garble windows slope keys).2.get index).slope = slope := by
  simp [garble, BitAdaptor.garble]

theorem evaluateValueGarbleEncode {count : Nat}
    (windows : Nat → BitAdaptor.FixedKeyOracle) (slope : BaseField)
    (keys : Vector BitAdaptor.Key count) (values : Fin count → Bool) :
    fromBits (fun index =>
      (evaluate windows values (garble windows slope keys).1 (encode keys values)).get index) =
      slope * bitValue values + bitsK (garble windows slope keys).2 := by
  rw [evaluateGarbleEncode]
  exact fromBitsSelectedOutputs slope _ (garbleSlope windows slope keys) values

end Kriterion.ArgoMAC.DigitAdaptor
