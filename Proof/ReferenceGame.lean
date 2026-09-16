/-
This file defines the reference game of one bridge key. The reference game
samples a tape, a carrier, and uniform raw coordinates; publishes the reference
table of the bridge key; runs the first adversary stage on the unprogrammed
oracle view; and, once the input is chosen, programs the fixed-key
permutations only at the selected labels: the three hash slots of a gate whose
bit is `false` take a uniform fiber sample of the gate's selected output, and
the two pad slots of a gate whose bit is `true` take the table row masked with
the selected output. The second stage then runs on the programmed view with
the honest labels. Unselected labels are never programmed and never used.
-/

import Proof.Reference

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit

/-! ### Partial programming of a fixed-key oracle -/

/-- One optional programming request per index: the label and the range it must map to. -/
abbrev Programs := FixedKeyIndex → Option (Block × Block)

/-- Program every requested index so that its label maps to its range; leave the other
indices unchanged. -/
def programIndices (programs : Programs) (oracle : PermutationOracle FixedKeyIndex Block) :
    PermutationOracle FixedKeyIndex Block where
  permutation index :=
    match programs index with
    | none => oracle.permutation index
    | some (label, range) =>
      (oracle.permutation index).trans (Equiv.swap (oracle.permutation index label) range)

theorem programIndices_none (programs : Programs) (oracle : PermutationOracle FixedKeyIndex Block)
    (index : FixedKeyIndex) (unrequested : programs index = none) :
    (programIndices programs oracle).permutation index = oracle.permutation index := by
  simp only [programIndices, unrequested]

theorem programIndices_some (programs : Programs) (oracle : PermutationOracle FixedKeyIndex Block)
    (index : FixedKeyIndex) (label range : Block) (requested : programs index = some (label, range)) :
    (programIndices programs oracle).permutation index =
      (oracle.permutation index).trans (Equiv.swap (oracle.permutation index label) range) := by
  simp only [programIndices, requested]

/-- A programmed index maps its label to its range. -/
theorem programIndices_apply_label (programs : Programs)
    (oracle : PermutationOracle FixedKeyIndex Block) (index : FixedKeyIndex) (label range : Block)
    (requested : programs index = some (label, range)) :
    (programIndices programs oracle).permutation index label = range := by
  rw [programIndices_some programs oracle index label range requested]
  simp

/-! ### The selected labels and the selected programs -/

/-- The label pair of one gate: the x key for the x adaptors, the y key for the y adaptors. -/
def gateKey (key : InputMacKey) (adaptor : CurveAdaptor) (position : Fin coordinateBitCount) :
    BitAdaptor.Key :=
  match adaptor with
  | .y4 | .y6 => key.y.get position
  | .x3 | .x5 | .x7 => key.x.get position

/-- The selected label of one gate. -/
def selectedLabel (key : InputMacKey) (input : AffineInput) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) : Block :=
  BitAdaptor.encode (gateKey key adaptor position) (inputBits input adaptor position)

/-- The 128-bit chunk of a digest that one slot must produce, fed forward through the label. -/
def slotRange (slot : FixedKeySlot) (hash : BitVec 384) (pad : BitAdaptor.Ciphertext)
    (label : Block) : Block :=
  match slot with
  | .hash chunk => hash.extractLsb' (128 * chunk.val) 128 ^^^ label
  | .pad chunk => pad.extractLsb' (128 * chunk.val) 128 ^^^ label

/-- The row of one gate in a table. -/
def tableRow (table : CurveMembership.Table) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) : BitAdaptor.Ciphertext :=
  ((tableRows table adaptor).get position).trueRow

/-- The programs of the reference game at the selected labels: hash slots of a `false` gate
take the fiber sample of the selected output, pad slots of a `true` gate take the row masked
with the selected output. -/
def selectedPrograms (key : InputMacKey) (input : AffineInput) (outputs : GateValues BaseField)
    (rows : GateValues BitAdaptor.Ciphertext) (fibers : GateValues (BitVec 384)) : Programs :=
  fun index =>
    let label := selectedLabel key input index.adaptor index.position
    match index.slot, inputBits input index.adaptor index.position with
    | .hash chunk, false =>
      some (label, slotRange (.hash chunk) (fibers index.adaptor index.position) 0 label)
    | .pad chunk, true =>
      some (label, slotRange (.pad chunk) 0
        (rows index.adaptor index.position ^^^
          BitAdaptor.fieldBytes (outputs index.adaptor index.position)) label)
    | _, _ => none

/-! ### Fiber samples of every gate -/

/-- The 384-bit strings, one per gate, whose field reductions are the given outputs. -/
abbrev HashFibers (outputs : GateValues BaseField) : Type :=
  { fibers : GateValues (BitVec 384) //
    ∀ adaptor position, ((fibers adaptor position).toNat : BaseField) = outputs adaptor position }

set_option exponentiation.threshold 400 in
instance (outputs : GateValues BaseField) : Nonempty (HashFibers outputs) :=
  ⟨⟨fun adaptor position => BitVec.ofNat 384 (outputs adaptor position).val, by
    intro adaptor position
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans (outputs adaptor position).val_lt (by decide)),
      ZMod.natCast_zmod_val]⟩⟩

noncomputable section

instance (outputs : GateValues BaseField) : Fintype (HashFibers outputs) :=
  Subtype.fintype _

/-- Uniform fiber samples of every gate. -/
def uniformHashFibers (outputs : GateValues BaseField) : PMF (GateValues (BitVec 384)) :=
  (PMF.uniformOfFintype (HashFibers outputs)).map Subtype.val

/-! ### The reference game -/

/-- The adversary type of the privacy games. -/
abbrev Adversary :=
  AdaptiveAdversary (publicOracleSpec FixedKeyIndex Garbling.EncIndex) AffineInput
    Garbling.Public LamportSignature Unit

/-- The state after the first stage: the chosen input, the adversary's state, and the
oracle state. -/
abbrev Selected (adversary : Adversary) := (AffineInput × adversary.State) × State

/-- The second-stage state: the first-stage state with its fixed-key oracle programmed at
the selected labels of `input`. -/
def programSelected (state : State) (input : AffineInput) (outputs : GateValues BaseField)
    (fibers : GateValues (BitVec 384)) : State :=
  { state with
    view := (programIndices (selectedPrograms state.inputMacKey input outputs
      (tableRow state.table) fibers) state.view.1, state.view.2) }

/-- The second stage of the reference game: sample the fiber of every gate, program the
selected labels, and run the adversary's decision on the honest labels. -/
def referenceStage2 (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (circuit : Garbling.Public) (outputs : GateValues BaseField)
    (selected : Selected adversary) : PMF Bool :=
  (uniformHashFibers outputs).bind fun fibers =>
    PMF.map Prod.fst ((adversary.decide parameter circuit
      (Lamport.selectedLabels (selected.2.inputMacKey.encodeAffine selected.1.1)) auxiliary
      selected.1.2).run idealOracle (programSelected selected.2 selected.1.1 outputs fibers))

/-- The reference game of the bridge key `bridge carrier`: a uniform tape, a uniform
carrier, and uniform raw coordinates; the first stage runs on the unprogrammed view; the
second stage programs the selected labels to the selected outputs of the chosen input. -/
def referenceGame (bridge : NonZeroBase → BaseField) (adversary : Adversary) (parameter : Nat)
    (auxiliary : Unit) : PMF Bool :=
  (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
    (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
      (PMF.uniformOfFintype Coordinates).bind fun raw =>
        let table := raw.table (bridge carrier) tape.inputMacKey
        ((adversary.chooseInput parameter (table, carrierBits carrier) auxiliary).run idealOracle
          (initialState tape table carrier)).bind fun selected =>
          referenceStage2 adversary parameter auxiliary (table, carrierBits carrier)
            (encodeCoordinates selected.1.1 raw).hash selected

/-! ### Basic facts -/

/-- An ideal-oracle run changes nothing but the log. -/
theorem run_idealOracle_support {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget)
    (state : State) (output : Result × State)
    (member : output ∈ (program.run idealOracle state).support) :
    output.2.view = state.view ∧ output.2.table = state.table ∧
      output.2.carrier = state.carrier ∧ output.2.inputMacKey = state.inputMacKey := by
  induction program generalizing state with
  | pure distribution =>
    rw [OracleProgram.run_pure, PMF.support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact ⟨rfl, rfl, rfl, rfl⟩
  | query request next inductionHypothesis =>
    rw [OracleProgram.run_query] at member
    obtain ⟨view, table, carrier, key⟩ :=
      inductionHypothesis (idealOracle request state).1 (idealOracle request state).2 member
    exact ⟨view, table, carrier, key⟩
  | sample distribution next inductionHypothesis =>
    rw [OracleProgram.run_sample, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨value, _, member⟩ := member
    exact inductionHypothesis value state member

theorem programSelected_log (state : State) (input : AffineInput)
    (outputs : GateValues BaseField) (fibers : GateValues (BitVec 384)) :
    (programSelected state input outputs fibers).log = state.log := rfl

theorem programSelected_view_snd (state : State) (input : AffineInput)
    (outputs : GateValues BaseField) (fibers : GateValues (BitVec 384)) :
    (programSelected state input outputs fibers).view.2 = state.view.2 := rfl

/-- The selected programs touch only the selected label of each index. -/
theorem selectedPrograms_label (key : InputMacKey) (input : AffineInput)
    (outputs : GateValues BaseField) (rows : GateValues BitAdaptor.Ciphertext)
    (fibers : GateValues (BitVec 384)) (index : FixedKeyIndex) (label range : Block)
    (requested : selectedPrograms key input outputs rows fibers index = some (label, range)) :
    label = selectedLabel key input index.adaptor index.position := by
  unfold selectedPrograms at requested
  simp only at requested
  split at requested <;> simp_all

/-- Hash slots are programmed exactly at `false` gates. -/
theorem selectedPrograms_hash (key : InputMacKey) (input : AffineInput)
    (outputs : GateValues BaseField) (rows : GateValues BitAdaptor.Ciphertext)
    (fibers : GateValues (BitVec 384)) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) (chunk : Fin 3) :
    selectedPrograms key input outputs rows fibers ⟨adaptor, position, .hash chunk⟩ =
      if inputBits input adaptor position then none
      else some (selectedLabel key input adaptor position,
        slotRange (.hash chunk) (fibers adaptor position) 0
          (selectedLabel key input adaptor position)) := by
  unfold selectedPrograms
  cases inputBits input adaptor position <;> rfl

/-- Pad slots are programmed exactly at `true` gates. -/
theorem selectedPrograms_pad (key : InputMacKey) (input : AffineInput)
    (outputs : GateValues BaseField) (rows : GateValues BitAdaptor.Ciphertext)
    (fibers : GateValues (BitVec 384)) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) (chunk : Fin 2) :
    selectedPrograms key input outputs rows fibers ⟨adaptor, position, .pad chunk⟩ =
      if inputBits input adaptor position then
        some (selectedLabel key input adaptor position,
          slotRange (.pad chunk) 0
            (rows adaptor position ^^^ BitAdaptor.fieldBytes (outputs adaptor position))
            (selectedLabel key input adaptor position))
      else none := by
  unfold selectedPrograms
  cases inputBits input adaptor position <;> rfl

end

end Kriterion.ArgoMAC.Security
