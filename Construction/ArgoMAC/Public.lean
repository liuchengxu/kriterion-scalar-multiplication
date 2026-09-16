/-
This file defines the public value of the design: the curve-membership table
paired with the 32-byte carrier. The garbler runs `CurveMembership.garble` on a
fresh finite tape. The released value on an on-curve input is exactly
`bridgeKey`, and the evaluator divides by it, so the tape stores the accepted
result of resampling `bridgeKey` until it is nonzero: a `NonZeroBase`. Zero is
impossible by type, and every tape field is a finite type.

The carrier is the field product `bridgeKey * scalar` in the base field. The
scalar modulus is smaller than the base modulus, so the scalar embeds without
reduction and the evaluator recovers it by one field division.
-/

import Construction.ArgoMAC.CurveMembership

namespace Kriterion.ArgoMAC

open BN254 Cryptography

/-- One curve-membership adaptor family. -/
inductive CurveAdaptor
  | y4 | y6 | x3 | x5 | x7
deriving DecidableEq

instance : Fintype CurveAdaptor :=
  ⟨{.y4, .y6, .x3, .x5, .x7}, fun value => by cases value <;> simp⟩

/-- A bucket has three hash permutations and two pad permutations. -/
inductive FixedKeySlot
  | hash (slot : Fin 3)
  | pad (slot : Fin 2)
deriving DecidableEq, Fintype

/-- This index selects one public fixed-key permutation: one adaptor family,
one coordinate bit position, and one slot. -/
structure FixedKeyIndex where
  adaptor : CurveAdaptor
  position : Fin coordinateBitCount
  slot : FixedKeySlot
deriving DecidableEq, Fintype

/-- The gate permutations of one adaptor family at one coordinate bit position. -/
def fixedKeyPermutations (oracle : PermutationOracle FixedKeyIndex Block)
    (adaptor : CurveAdaptor) (position : Nat) : BitAdaptor.FixedKeyPermutations := {
  hash := fun slot => oracle.permutation {
    adaptor
    position := ⟨position % coordinateBitCount, Nat.mod_lt _ (by decide)⟩
    slot := .hash slot }
  pad := fun slot => oracle.permutation {
    adaptor
    position := ⟨position % coordinateBitCount, Nat.mod_lt _ (by decide)⟩
    slot := .pad slot }
}

/-- This oracle serves the gate of one adaptor family at one bit position. -/
def fixedKeyGate (oracle : PermutationOracle FixedKeyIndex Block)
    (adaptor : CurveAdaptor) (position : Nat) : BitAdaptor.FixedKeyOracle :=
  BitAdaptor.fixedKeyOracle (fixedKeyPermutations oracle adaptor position)

/-- Each adaptor family reads its own window family. -/
def curveOracles (oracle : PermutationOracle FixedKeyIndex Block) :
    CurveMembership.Oracles := {
  y4 := fixedKeyGate oracle .y4
  y6 := fixedKeyGate oracle .y6
  x3 := fixedKeyGate oracle .x3
  x5 := fixedKeyGate oracle .x5
  x7 := fixedKeyGate oracle .x7
}

namespace Garbling

/-- The public value: the curve-membership table and the 32-byte carrier. -/
abbrev Public := CurveMembership.Table × BitVec 256

/-- The construction reads no encryption permutation. The public game still
exposes one, so the tape carries a single unused family. -/
abbrev EncIndex := Unit

/-- This structure contains every explicit garbling input. Every field is a
finite type. `bridgeKey` stores the accepted value of resampling until nonzero.
`encOracle` and `hashOracle` are the public oracles the construction never
queries. -/
structure Randomness where
  bridgeKey : NonZeroBase
  curveMask : NonZeroBase
  curveR1 : BaseField
  curveR2 : BaseField
  fixedKeyOracle : PermutationOracle FixedKeyIndex Block
  inputMacKey : InputMacKey
  encOracle : PermutationOracle EncIndex Block
  hashOracle : BaseField → Block × Block

/-- The private garbling output: the scalar and the complete tape. -/
structure EncodingKey where
  scalar : NonZeroScalar
  randomness : Randomness

/-- The carrier packs the base-field product `bridgeKey * scalar`. -/
def maskScalar (bridgeKey : NonZeroBase) (scalar : NonZeroScalar) : BitVec 256 :=
  BitVec.ofNat 256 (bridgeKey.value * (scalar.value.val : BaseField)).val

/-- The garbler builds the curve-membership table on the tape's coins and
releases the masked scalar beside it. -/
def garble (_parameter : Nat) (scalar : NonZeroScalar) (randomness : Randomness) :
    Public × EncodingKey :=
  ((CurveMembership.garble randomness.bridgeKey.value randomness.curveMask.value
      randomness.curveR1 randomness.curveR2
      (curveOracles randomness.fixedKeyOracle) randomness.inputMacKey,
    maskScalar randomness.bridgeKey scalar),
   { scalar, randomness })

end Garbling
end Kriterion.ArgoMAC
