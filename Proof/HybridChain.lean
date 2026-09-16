/-
This file walks the hybrid game to the reference game of its own bridge key.

The hybrid game garbles the real curve table on the tape's fixed-key oracle and
runs both adversary stages on that same oracle. The reference game publishes a
table built from fresh per-gate secrets, runs the first stage on an
unprogrammed oracle, and programs only the selected labels of the chosen input.
Three hops close the gap. First the oracle is reparametrised: a uniform oracle
is a uniform oracle programmed at every label garbling reads, so the real table
becomes the reference table of the fresh digests and pads. Then the programmed
view is replaced by the unprogrammed one in the first stage and by the
selected-label programming in the second; both replacements are invisible until
a logged query hits one of the two hidden label values of its own gate. Finally
the fresh digests are replaced by a field element and a fiber sample, and the
nonzero mask by a uniform one.
-/

import Proof.Chain
import Proof.GameShape
import Proof.Privacy
import Proof.Reparametrise

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

noncomputable section

/-! ### The label key as a separate sample -/

/-- The tape with its label key replaced. The first hop programs the oracle at labels of
the key, so the key must be sampled before the oracle. -/
def setKey (tape : Garbling.Randomness) (key : InputMacKey) : Garbling.Randomness :=
  { tape with inputMacKey := key }

/-- Exchanging a tape's label key with a separate sample is an involution. -/
def swapKey : Garbling.Randomness × InputMacKey ≃ Garbling.Randomness × InputMacKey where
  toFun pair := (setKey pair.1 pair.2, pair.1.inputMacKey)
  invFun pair := (setKey pair.1 pair.2, pair.1.inputMacKey)
  left_inv pair := by
    obtain ⟨tape, _⟩ := pair
    cases tape
    rfl
  right_inv pair := by
    obtain ⟨tape, _⟩ := pair
    cases tape
    rfl

/-- A uniform tape with a fresh uniform label key is a uniform tape. -/
theorem uniform_bind_setKey {Outcome : Type} (continuation : Garbling.Randomness → PMF Outcome) :
    ((PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype InputMacKey).bind fun key => continuation (setKey tape key)) =
      (PMF.uniformOfFintype Garbling.Randomness).bind continuation := by
  rw [uniformOfFintype_bind_prod]
  have swapped := uniformOfFintype_bind_equiv swapKey
    fun pair : Garbling.Randomness × InputMacKey => continuation pair.1
  simp only [swapKey, Equiv.coe_fn_mk] at swapped
  have unprod : ((PMF.uniformOfFintype (Garbling.Randomness × InputMacKey)).bind fun pair =>
      continuation pair.1) =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype InputMacKey).bind fun _ => continuation tape :=
    (uniformOfFintype_bind_prod fun tape (_ : InputMacKey) => continuation tape).symm
  rw [swapped, unprod]
  simp only [PMF.bind_const]

/-! ### The hybrid game in two-stage shape -/

/-- A state that an ideal-oracle run left is the second-stage state of its own log. -/
theorem eq_stageTwoState (view : View) (table : CurveMembership.Table) (carrier : NonZeroBase)
    (key : InputMacKey) (state : State) (sameView : state.view = view)
    (sameTable : state.table = table) (sameCarrier : state.carrier = carrier)
    (sameKey : state.inputMacKey = key) :
    state = stageTwoState view state.log table carrier key := by
  obtain ⟨view', log, table', carrier', key'⟩ := state
  simp only at sameView sameTable sameCarrier sameKey
  subst sameView
  subst sameTable
  subst sameCarrier
  subst sameKey
  rfl

/-- A hybrid-shaped game: the first stage runs on `firstView`, the second stage on
`secondView` with the honest labels of `key`. The two views coincide in the hybrid game
itself; the first hop of the chain separates them. -/
def hybridTwoStage (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (circuit : Garbling.Public) (carrier : NonZeroBase) (key : InputMacKey)
    (firstView secondView : View) : PMF Bool :=
  (loggedFirstStage adversary parameter auxiliary circuit firstView).bind fun outcome =>
    (hybridStageTwo adversary parameter auxiliary circuit outcome.1.1 outcome.1.2
      (stageTwoState secondView outcome.2 circuit.1 carrier key)).map Prod.fst

/-- One round of the hybrid game on explicit coordinates: the table is garbled on the
view's own fixed-key oracle and both stages run on that view. -/
def hybridOn (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (bridgeKey mask r1 r2 : BaseField) (carrier : NonZeroBase) (key : InputMacKey)
    (view : View) : PMF Bool :=
  hybridTwoStage adversary parameter auxiliary
    (CurveMembership.garble bridgeKey mask r1 r2 (curveOracles view.1) key, carrierBits carrier)
    carrier key view view

/-- The hybrid game is one round of `hybridOn` on a uniform tape and carrier. -/
theorem hybridGame_eq_hybridOn [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) (hybridSimulator scalar)
        idealOracle adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
          hybridOn adversary parameter auxiliary ((mulScalar scalar).symm carrier).value
            tape.curveMask.value tape.curveR1 tape.curveR2 carrier tape.inputMacKey
            (Garbling.evaluationOracle tape) := by
  rw [hybridGame_eq]
  refine congrArg (PMF.bind _) (funext fun tape => ?_)
  refine congrArg (PMF.bind _) (funext fun carrier => ?_)
  set table := curveTable (setBridge tape ((mulScalar scalar).symm carrier)) with tableEq
  have conditioned : ((adversary.chooseInput parameter (table, carrierBits carrier)
        auxiliary).run idealOracle (initialState tape table carrier)).bind (fun selected =>
      (hybridStageTwo adversary parameter auxiliary (table, carrierBits carrier) selected.1.1
        selected.1.2 selected.2).map Prod.fst) =
      ((adversary.chooseInput parameter (table, carrierBits carrier)
        auxiliary).run idealOracle (initialState tape table carrier)).bind (fun selected =>
      (hybridStageTwo adversary parameter auxiliary (table, carrierBits carrier) selected.1.1
        selected.1.2 (stageTwoState (Garbling.evaluationOracle tape) selected.2.log table
          carrier tape.inputMacKey)).map Prod.fst) := by
    refine bind_congr_support fun selected member => ?_
    obtain ⟨sameView, sameTable, sameCarrier, sameKey⟩ :=
      run_idealOracle_support _ _ selected member
    rw [← eq_stageTwoState (Garbling.evaluationOracle tape) table carrier tape.inputMacKey
      selected.2 sameView sameTable sameCarrier sameKey]
  have circuitEq : (CurveMembership.garble ((mulScalar scalar).symm carrier).value
      tape.curveMask.value tape.curveR1 tape.curveR2
      (curveOracles (Garbling.evaluationOracle tape).1) tape.inputMacKey,
      carrierBits carrier) = (table, carrierBits carrier) := rfl
  rw [conditioned]
  unfold hybridOn hybridTwoStage
  rw [circuitEq, ← map_loggedOutcome_firstState adversary parameter auxiliary
    (table, carrierBits carrier) (Garbling.evaluationOracle tape) table carrier
    tape.inputMacKey, PMF.bind_map]
  rfl

/-- The hybrid game with the label key, the fixed-key oracle and the curve coordinates
sampled separately from the rest of the tape. -/
theorem hybridGame_eq_split [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) (hybridSimulator scalar)
        idealOracle adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype InputMacKey).bind fun key =>
          (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
            (PMF.uniformOfFintype (NonZeroBase × BaseField × BaseField)).bind fun curve =>
              (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
                hybridOn adversary parameter auxiliary ((mulScalar scalar).symm carrier).value
                  curve.1.value curve.2.1 curve.2.2 carrier key
                  (oracle, tape.encOracle, tape.hashOracle) := by
  rw [hybridGame_eq_hybridOn, ← uniform_bind_setCurve, ← uniform_bind_setOracle,
    ← uniform_bind_setKey]
  rfl

/-! ### The fresh secrets of the reparametrisation -/

/-- The fresh 128-bit value one index carries, before it is fed forward through the label
garbling reads it at. -/
def freshValue (digests : GateValues (BitVec 384)) (pads : GateValues BitAdaptor.Ciphertext)
    (index : FixedKeyIndex) : Block :=
  match index.slot with
  | .hash chunk => (digests index.adaptor index.position).extractLsb' (128 * chunk.val) 128
  | .pad chunk => (pads index.adaptor index.position).extractLsb' (128 * chunk.val) 128

theorem freshOfSecrets_eq (key : InputMacKey) (digests : GateValues (BitVec 384))
    (pads : GateValues BitAdaptor.Ciphertext) (index : FixedKeyIndex) :
    freshOfSecrets key digests pads index = freshValue digests pads index ^^^ usedLabel key index := by
  obtain ⟨adaptor, position, slot⟩ := index
  cases slot <;> rfl

/-- The programs of the first hop: every index is programmed at the label garbling reads
it at, to its fresh value fed forward through that label. -/
def usedPrograms (key : InputMacKey) (values : FixedKeyIndex → Block) : Programs :=
  fun index => some (usedLabel key index, values index ^^^ usedLabel key index)

/-- The reparametrised oracle is the family programming at the used labels. -/
theorem programFamily_eq_programIndices (key : InputMacKey)
    (oracle : PermutationOracle FixedKeyIndex Block) (digests : GateValues (BitVec 384))
    (pads : GateValues BitAdaptor.Ciphertext) :
    (programFamily (usedLabel key) (oracle, freshOfSecrets key digests pads)).1 =
      programIndices (usedPrograms key (freshValue digests pads)) oracle := by
  refine congrArg PermutationOracle.mk (funext fun index => ?_)
  simp only [usedPrograms, programAt, freshOfSecrets_eq]

/-- The field element a fresh digest reduces to. -/
def digestField (digests : GateValues (BitVec 384)) : GateValues BaseField :=
  fun adaptor position => ((digests adaptor position).toNat : BaseField)

theorem freshHash_freshOfSecrets (key : InputMacKey) (digests : GateValues (BitVec 384))
    (pads : GateValues BitAdaptor.Ciphertext) :
    freshHash key (freshOfSecrets key digests pads) = digestField digests := by
  have base : freshDigest key (freshOfSecrets key digests pads) = digests :=
    congrArg Prod.fst ((freshEquiv key).right_inv (digests, pads))
  funext adaptor position
  rw [freshHash, base]
  rfl

theorem freshPad_freshOfSecrets (key : InputMacKey) (digests : GateValues (BitVec 384))
    (pads : GateValues BitAdaptor.Ciphertext) :
    freshPad key (freshOfSecrets key digests pads) = pads :=
  congrArg Prod.snd ((freshEquiv key).right_inv (digests, pads))

/-! ### The first hop: reparametrise the oracle -/

/-- A uniform fixed-key oracle is a uniform oracle programmed at every index's own label
to an independent uniform value. -/
theorem uniform_bind_programFamily {Outcome : Type} (labels : FixedKeyIndex → Block)
    (continuation : PermutationOracle FixedKeyIndex Block → PMF Outcome) :
    ((PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype (FixedKeyIndex → Block)).bind fun fresh =>
          continuation (programFamily labels (oracle, fresh)).1) =
      (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind continuation := by
  rw [uniformOfFintype_bind_prod]
  conv_rhs => rw [← uniform_programFamily labels]
  rw [PMF.bind_map]
  rfl

/-- A uniform fresh family is a uniform digest and a uniform pad for every gate. -/
theorem uniform_bind_freshOfSecrets {Outcome : Type} (key : InputMacKey)
    (continuation : (FixedKeyIndex → Block) → PMF Outcome) :
    ((PMF.uniformOfFintype (GateValues (BitVec 384) ×
          GateValues BitAdaptor.Ciphertext)).bind fun secrets =>
        continuation (freshOfSecrets key secrets.1 secrets.2)) =
      (PMF.uniformOfFintype (FixedKeyIndex → Block)).bind continuation := by
  conv_lhs => rw [← uniform_map_freshEquiv key]
  rw [PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun fresh => ?_)
  exact congrArg continuation ((freshEquiv key).left_inv fresh)

/-- A uniform fixed-key oracle is a uniform oracle programmed at every used label to a
fresh uniform digest and pad of every gate. -/
theorem uniform_bind_usedPrograms {Outcome : Type} (key : InputMacKey)
    (continuation : PermutationOracle FixedKeyIndex Block → PMF Outcome) :
    ((PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype (GateValues (BitVec 384) ×
            GateValues BitAdaptor.Ciphertext)).bind fun secrets =>
          continuation (programFamily (usedLabel key)
            (oracle, freshOfSecrets key secrets.1 secrets.2)).1) =
      (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind continuation := by
  rw [← uniform_bind_programFamily (usedLabel key) continuation]
  exact congrArg (PMF.bind _) (funext fun oracle =>
    uniform_bind_freshOfSecrets key fun fresh =>
      continuation (programFamily (usedLabel key) (oracle, fresh)).1)

/-- The H side after the first hop: the oracle is programmed at every used label to the
fresh value of that slot, and the released table is the reference table of the fresh
per-gate digests and pads. -/
def hybridFresh (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (bridgeKey : BaseField) (carrier : NonZeroBase) (key : InputMacKey)
    (rest : PermutationOracle Garbling.EncIndex Block × (BaseField → Block × Block))
    (oracle : PermutationOracle FixedKeyIndex Block) (mask r1 r2 : BaseField)
    (secrets : GateValues (BitVec 384) × GateValues BitAdaptor.Ciphertext) : PMF Bool :=
  hybridTwoStage adversary parameter auxiliary
    (Coordinates.table bridgeKey key ⟨mask, r1, r2, digestField secrets.1, secrets.2⟩,
      carrierBits carrier) carrier key
    (programIndices (usedPrograms key (freshValue secrets.1 secrets.2)) oracle, rest)
    (programIndices (usedPrograms key (freshValue secrets.1 secrets.2)) oracle, rest)

/-- Step 1 of the chain, exact: the hybrid game is the reparametrised game. -/
theorem hybridGame_eq_fresh [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) (hybridSimulator scalar)
        idealOracle adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype InputMacKey).bind fun key =>
          (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
            (PMF.uniformOfFintype (GateValues (BitVec 384) ×
                GateValues BitAdaptor.Ciphertext)).bind fun secrets =>
              (PMF.uniformOfFintype (NonZeroBase × BaseField × BaseField)).bind fun curve =>
                (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
                  hybridFresh adversary parameter auxiliary
                    ((mulScalar scalar).symm carrier).value carrier key
                    (tape.encOracle, tape.hashOracle) oracle curve.1.value curve.2.1 curve.2.2
                    secrets := by
  rw [hybridGame_eq_split]
  refine congrArg (PMF.bind _) (funext fun tape => ?_)
  refine congrArg (PMF.bind _) (funext fun key => ?_)
  rw [← uniform_bind_usedPrograms key]
  refine congrArg (PMF.bind _) (funext fun oracle => ?_)
  refine congrArg (PMF.bind _) (funext fun secrets => ?_)
  refine congrArg (PMF.bind _) (funext fun curve => ?_)
  refine congrArg (PMF.bind _) (funext fun carrier => ?_)
  unfold hybridOn hybridFresh
  rw [show (curveOracles ((programFamily (usedLabel key)
        (oracle, freshOfSecrets key secrets.1 secrets.2)).1, tape.encOracle, tape.hashOracle).1) =
      curveOracles (programFamily (usedLabel key)
        (oracle, freshOfSecrets key secrets.1 secrets.2)).1 from rfl,
    curveGarble_programFamily, freshHash_freshOfSecrets, freshPad_freshOfSecrets,
    programFamily_eq_programIndices]

end

end Kriterion.ArgoMAC.Security
