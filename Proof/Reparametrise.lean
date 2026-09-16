/-
This file proves the algebraic half of the first hop of the chain: the real
table on a reparametrised fixed-key oracle is a reference table.

Garbling reads each gate's fixed-key permutations at exactly two labels: the
three hash slots at the gate's false label and the two pad slots at its true
label. Programming every index at that label to a fresh value therefore makes
the Davies--Meyer hash of the false label the concatenation of the three fresh
chunks, and the pad of the true label the concatenation of the two fresh
chunks. Both are then independent of the labels, so the garbled table is
exactly the reference table whose per-gate secrets are those two values.
-/

import Proof.DeferredSteering
import Proof.Programming

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

/-! ### The label each index is garbled at -/

/-- The label garbling reads at one fixed-key index: hash slots read their gate's false
label, pad slots read its true label. -/
def usedLabel (key : InputMacKey) (index : FixedKeyIndex) : Block :=
  match index.slot with
  | .hash _ => (gateKey key index.adaptor index.position).falseLabel
  | .pad _ => (gateKey key index.adaptor index.position).trueLabel

/-- A programmed index maps its own label to its fresh value. -/
theorem programFamily_apply (labels : FixedKeyIndex → Block)
    (pair : PermutationOracle FixedKeyIndex Block × (FixedKeyIndex → Block))
    (index : FixedKeyIndex) :
    (programFamily labels pair).1.permutation index (labels index) = pair.2 index := by
  simp only [programFamily, programAt, Equiv.trans_apply, Equiv.swap_apply_left]

/-! ### The fresh secrets of one gate -/

/-- The digest the fresh hash chunks of one gate produce at its false label. -/
def freshDigest (key : InputMacKey) (fresh : FixedKeyIndex → Block) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) : BitVec 384 :=
  (fresh ⟨adaptor, position, .hash 2⟩ ^^^ (gateKey key adaptor position).falseLabel) ++
    (fresh ⟨adaptor, position, .hash 1⟩ ^^^ (gateKey key adaptor position).falseLabel) ++
      (fresh ⟨adaptor, position, .hash 0⟩ ^^^ (gateKey key adaptor position).falseLabel)

/-- The pad the fresh pad chunks of one gate produce at its true label. -/
def freshPad (key : InputMacKey) (fresh : FixedKeyIndex → Block) :
    GateValues BitAdaptor.Ciphertext :=
  fun adaptor position =>
    (fresh ⟨adaptor, position, .pad 1⟩ ^^^ (gateKey key adaptor position).trueLabel) ++
      (fresh ⟨adaptor, position, .pad 0⟩ ^^^ (gateKey key adaptor position).trueLabel)

/-- The field element the fresh digest of one gate reduces to. -/
def freshHash (key : InputMacKey) (fresh : FixedKeyIndex → Block) : GateValues BaseField :=
  fun adaptor position => ((freshDigest key fresh adaptor position).toNat : BaseField)

/-! ### The programmed gate is a secret gate -/

theorem hashBytes_programFamily (oracle : PermutationOracle FixedKeyIndex Block)
    (key : InputMacKey) (fresh : FixedKeyIndex → Block) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) :
    BitAdaptor.hashBytes
        (fixedKeyPermutations (programFamily (usedLabel key) (oracle, fresh)).1 adaptor
          position.val) (gateKey key adaptor position).falseLabel =
      freshDigest key fresh adaptor position := by
  have slot (chunk : Fin 3) :
      (programFamily (usedLabel key) (oracle, fresh)).1.permutation
          ⟨adaptor, position, .hash chunk⟩ (gateKey key adaptor position).falseLabel =
        fresh ⟨adaptor, position, .hash chunk⟩ :=
    programFamily_apply (usedLabel key) (oracle, fresh) ⟨adaptor, position, .hash chunk⟩
  simp only [BitAdaptor.hashBytes, fixedKeyPermutations_val, daviesMeyer, Cryptography.xor,
    slot, freshDigest]

theorem padBytes_programFamily (oracle : PermutationOracle FixedKeyIndex Block)
    (key : InputMacKey) (fresh : FixedKeyIndex → Block) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) :
    BitAdaptor.padBytes
        (fixedKeyPermutations (programFamily (usedLabel key) (oracle, fresh)).1 adaptor
          position.val) (gateKey key adaptor position).trueLabel =
      freshPad key fresh adaptor position := by
  have slot (chunk : Fin 2) :
      (programFamily (usedLabel key) (oracle, fresh)).1.permutation
          ⟨adaptor, position, .pad chunk⟩ (gateKey key adaptor position).trueLabel =
        fresh ⟨adaptor, position, .pad chunk⟩ :=
    programFamily_apply (usedLabel key) (oracle, fresh) ⟨adaptor, position, .pad chunk⟩
  simp only [BitAdaptor.padBytes, fixedKeyPermutations_val, daviesMeyer, Cryptography.xor,
    slot, freshPad]

/-- One gate of the reparametrised oracle garbles exactly as the secret gate of its two
fresh values. -/
theorem garble_programFamily (oracle : PermutationOracle FixedKeyIndex Block)
    (key : InputMacKey) (fresh : FixedKeyIndex → Block) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) (slope : BaseField) :
    BitAdaptor.garble
        (fixedKeyGate (programFamily (usedLabel key) (oracle, fresh)).1 adaptor position.val)
        slope (gateKey key adaptor position) =
      BitAdaptor.garble
        (secretOracle (freshHash key fresh adaptor position) (freshPad key fresh adaptor position))
        slope (gateKey key adaptor position) := by
  simp only [BitAdaptor.garble, fixedKeyGate, BitAdaptor.fixedKeyOracle, secretOracle,
    hashBytes_programFamily, padBytes_programFamily, freshHash]

/-- One adaptor family of the reparametrised oracle garbles exactly as its secret family. -/
theorem digitGarble_programFamily (oracle : PermutationOracle FixedKeyIndex Block)
    (key : InputMacKey) (fresh : FixedKeyIndex → Block) (adaptor : CurveAdaptor)
    (slope : BaseField) :
    DigitAdaptor.garble
        (fixedKeyGate (programFamily (usedLabel key) (oracle, fresh)).1 adaptor) slope
        (coordinateKey key (adaptorCoordinate adaptor)) =
      DigitAdaptor.garble
        (secretWindows (freshHash key fresh) (freshPad key fresh) adaptor) slope
        (coordinateKey key (adaptorCoordinate adaptor)) := by
  have same : (Vector.ofFn fun index : Fin coordinateBitCount =>
        BitAdaptor.garble
          (fixedKeyGate (programFamily (usedLabel key) (oracle, fresh)).1 adaptor index.val) slope
          ((coordinateKey key (adaptorCoordinate adaptor)).get index)) =
      Vector.ofFn fun index : Fin coordinateBitCount =>
        BitAdaptor.garble
          (secretWindows (freshHash key fresh) (freshPad key fresh) adaptor index.val) slope
          ((coordinateKey key (adaptorCoordinate adaptor)).get index) := by
    refine congrArg Vector.ofFn (funext fun index => ?_)
    rw [secretWindows_val, ← gateKey_eq]
    exact garble_programFamily oracle key fresh adaptor index slope
  simp only [DigitAdaptor.garble, same]

/-- The first hop's table identity: the real curve table on the reparametrised oracle is
the reference table of the fresh per-gate secrets. -/
theorem curveGarble_programFamily (bridgeKey mask r1 r2 : BaseField)
    (oracle : PermutationOracle FixedKeyIndex Block) (key : InputMacKey)
    (fresh : FixedKeyIndex → Block) :
    CurveMembership.garble bridgeKey mask r1 r2
        (curveOracles (programFamily (usedLabel key) (oracle, fresh)).1) key =
      Coordinates.table bridgeKey key
        ⟨mask, r1, r2, freshHash key fresh, freshPad key fresh⟩ := by
  have y4 : ∀ slope : BaseField,
      DigitAdaptor.garble
          (fixedKeyGate (programFamily (usedLabel key) (oracle, fresh)).1 .y4) slope key.y =
        DigitAdaptor.garble
          (secretWindows (freshHash key fresh) (freshPad key fresh) .y4) slope key.y :=
    fun slope => digitGarble_programFamily oracle key fresh .y4 slope
  have y6 : ∀ slope : BaseField,
      DigitAdaptor.garble
          (fixedKeyGate (programFamily (usedLabel key) (oracle, fresh)).1 .y6) slope key.y =
        DigitAdaptor.garble
          (secretWindows (freshHash key fresh) (freshPad key fresh) .y6) slope key.y :=
    fun slope => digitGarble_programFamily oracle key fresh .y6 slope
  have x3 : ∀ slope : BaseField,
      DigitAdaptor.garble
          (fixedKeyGate (programFamily (usedLabel key) (oracle, fresh)).1 .x3) slope key.x =
        DigitAdaptor.garble
          (secretWindows (freshHash key fresh) (freshPad key fresh) .x3) slope key.x :=
    fun slope => digitGarble_programFamily oracle key fresh .x3 slope
  have x5 : ∀ slope : BaseField,
      DigitAdaptor.garble
          (fixedKeyGate (programFamily (usedLabel key) (oracle, fresh)).1 .x5) slope key.x =
        DigitAdaptor.garble
          (secretWindows (freshHash key fresh) (freshPad key fresh) .x5) slope key.x :=
    fun slope => digitGarble_programFamily oracle key fresh .x5 slope
  have x7 : ∀ slope : BaseField,
      DigitAdaptor.garble
          (fixedKeyGate (programFamily (usedLabel key) (oracle, fresh)).1 .x7) slope key.x =
        DigitAdaptor.garble
          (secretWindows (freshHash key fresh) (freshPad key fresh) .x7) slope key.x :=
    fun slope => digitGarble_programFamily oracle key fresh .x7 slope
  simp only [Coordinates.table, CurveMembership.garble, curveOracles, secretOracles,
    y4, y6, x3, x5, x7]

end Kriterion.ArgoMAC.Security
