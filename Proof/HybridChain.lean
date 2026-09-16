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

/-! ### The bad queries of an oracle hop -/

/-- The label coordinate of a query's own gate: the coordinate and bit position of its
index, and the label value that index's slot reads. -/
def queryLabelIndex (query : Query) : Option (Bool × Fin coordinateBitCount × Bool) :=
  (queryIndex query).map fun index =>
    (adaptorCoordinate index.adaptor, index.position, slotBit index.slot)

/-- The label values at which one query sees a programming of its own index to the given
fresh value. -/
def usedHidden (oracle : PermutationOracle FixedKeyIndex Block)
    (values : FixedKeyIndex → Block) : Query → Finset Block
  | .fixedForward index input => forwardHidden (oracle.permutation index) (values index) input
  | .fixedInverse index output => inverseHidden (oracle.permutation index) (values index) output
  | _ => ∅

theorem usedHidden_card (oracle : PermutationOracle FixedKeyIndex Block)
    (values : FixedKeyIndex → Block) (query : Query) :
    (usedHidden oracle values query).card ≤ 2 := by
  cases query with
  | fixedForward index input => exact forwardHidden_card _ _ _
  | fixedInverse index output => exact inverseHidden_card _ _ _
  | encForward _ _ => simp [usedHidden]
  | encInverse _ _ => simp [usedHidden]
  | hash _ => simp [usedHidden]

/-- A query is bad for a family programming when the label of its own gate is one of the
hidden label values of the query. -/
def UsedBad (oracle : PermutationOracle FixedKeyIndex Block) (values : FixedKeyIndex → Block)
    (key : InputMacKey) (query : Query) : Prop :=
  ∃ coordinate position value, queryLabelIndex query = some (coordinate, position, value) ∧
    keyLabel key coordinate position value ∈ usedHidden oracle values query

/-- The label garbling reads one index at is that index's own key label. -/
theorem usedLabel_eq_keyLabel (key : InputMacKey) (index : FixedKeyIndex) :
    usedLabel key index =
      keyLabel key (adaptorCoordinate index.adaptor) index.position (slotBit index.slot) := by
  obtain ⟨adaptor, position, slot⟩ := index
  cases slot <;> simp [usedLabel, keyLabel, slotBit, gateKey_eq, BitAdaptor.encode]

/-- Off its bad label values, a query cannot tell the family programming at the used
labels from the unprogrammed oracle. -/
theorem publicAnswer_usedPrograms (oracle : PermutationOracle FixedKeyIndex Block)
    (rest : PermutationOracle Garbling.EncIndex Block × (BaseField → Block × Block))
    (key : InputMacKey) (values : FixedKeyIndex → Block) (query : Query)
    (good : ¬ UsedBad oracle values key query) :
    publicAnswer (programIndices (usedPrograms key values) oracle, rest) query =
      publicAnswer (oracle, rest) query := by
  cases query with
  | fixedForward index input =>
    have missing : usedLabel key index ∉
        forwardHidden (oracle.permutation index) (values index) input := by
      rw [usedLabel_eq_keyLabel]
      intro member
      exact good ⟨adaptorCoordinate index.adaptor, index.position, slotBit index.slot, rfl, member⟩
    show (programIndices (usedPrograms key values) oracle).permutation index input =
      oracle.permutation index input
    rw [programIndices_eq_programmed (usedPrograms key values) oracle index (usedLabel key index)
      (values index ^^^ usedLabel key index) rfl]
    exact programmed_apply_of_not_mem _ _ _ _ missing
  | fixedInverse index output =>
    have missing : usedLabel key index ∉
        inverseHidden (oracle.permutation index) (values index) output := by
      rw [usedLabel_eq_keyLabel]
      intro member
      exact good ⟨adaptorCoordinate index.adaptor, index.position, slotBit index.slot, rfl, member⟩
    show ((programIndices (usedPrograms key values) oracle).permutation index).symm output =
      (oracle.permutation index).symm output
    rw [programIndices_eq_programmed (usedPrograms key values) oracle index (usedLabel key index)
      (values index ^^^ usedLabel key index) rfl]
    exact programmed_symm_apply_of_not_mem _ _ _ _ missing
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash _ => rfl

/-! ### The first oracle hop: the first stage moves to the unprogrammed view -/

/-- A sample built from the label key and the key-free data splits back into its two
binds. -/
theorem bind_pairLaw {Data Outcome : Type} (data : PMF Data)
    (continuation : InputMacKey × Data → PMF Outcome) :
    (((PMF.uniformOfFintype InputMacKey).bind fun key =>
        data.map fun datum => (key, datum)).bind continuation) =
      (PMF.uniformOfFintype InputMacKey).bind fun key => data.bind fun datum =>
        continuation (key, datum) := by
  rw [PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun key => ?_)
  rw [PMF.bind_map]
  rfl

/-- The bad event of an oracle hop: some entry of the stage's log is bad. -/
def firstBad {Data : Type} (adversary : Adversary) (view : Data → View)
    (values : Data → FixedKeyIndex → Block) :
    Set ((InputMacKey × Data) × ((AffineInput × adversary.State) × List Query)) :=
  {pair | ∃ query ∈ pair.2.2, UsedBad (view pair.1.2).1 (values pair.1.2) pair.1.1 query}

/-- Two blocks of a query budget over `2 ^ 128`, as a real number. -/
theorem toReal_two_budget (budget : Nat) :
    (((2 : ENNReal) * (budget : ENNReal) / 2 ^ 128)).toReal = 2 * (budget : ℝ) / 2 ^ 128 := by
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]

/-- Hop A. Replacing the programmed first-stage view by the unprogrammed one is invisible
until a logged query hits one of the two hidden label values of its own gate; the label is
independent of the unprogrammed run, so that costs `2 q₁ / 2 ^ 128`. -/
theorem advantage_firstView_le {Data : Type} (adversary : Adversary) (parameter : Nat)
    (auxiliary : Unit) (data : PMF Data) (view : Data → View)
    (circuit : Data → Garbling.Public) (carrier : Data → NonZeroBase)
    (values : Data → FixedKeyIndex → Block)
    (continuation : InputMacKey → Data →
      (AffineInput × adversary.State) × List Query → PMF Bool) :
    advantage
        ((PMF.uniformOfFintype InputMacKey).bind fun key => data.bind fun datum =>
          (loggedFirstStage adversary parameter auxiliary (circuit datum)
              (programIndices (usedPrograms key (values datum)) (view datum).1,
                (view datum).2)).bind (continuation key datum))
        ((PMF.uniformOfFintype InputMacKey).bind fun key => data.bind fun datum =>
          (loggedFirstStage adversary parameter auxiliary (circuit datum) (view datum)).bind
            (continuation key datum)) ≤
      2 * (adversary.firstQueryBudget parameter : ℝ) / 2 ^ 128 := by
  rw [← bind_pairLaw data fun sample =>
      (loggedFirstStage adversary parameter auxiliary (circuit sample.2)
        (programIndices (usedPrograms sample.1 (values sample.2)) (view sample.2).1,
          (view sample.2).2)).bind (continuation sample.1 sample.2),
    ← bind_pairLaw data fun sample =>
      (loggedFirstStage adversary parameter auxiliary (circuit sample.2) (view sample.2)).bind
        (continuation sample.1 sample.2)]
  refine le_trans (advantage_bind_le_jointBad
    ((PMF.uniformOfFintype InputMacKey).bind fun key => data.map fun datum => (key, datum))
    (fun sample => loggedFirstStage adversary parameter auxiliary (circuit sample.2)
      (programIndices (usedPrograms sample.1 (values sample.2)) (view sample.2).1,
        (view sample.2).2))
    (fun sample => loggedFirstStage adversary parameter auxiliary (circuit sample.2)
      (view sample.2))
    (fun sample => continuation sample.1 sample.2) (firstBad adversary view values) ?_) ?_
  · rintro ⟨⟨key, datum⟩, result, log⟩ good
    have goodQuery : ∀ query ∈ log, ¬ UsedBad (view datum).1 (values datum) key query := by
      intro query member bad
      exact good ⟨query, member, bad⟩
    show ((((adversary.chooseInput parameter (circuit datum) auxiliary).run idealOracle
        (firstState (programIndices (usedPrograms key (values datum)) (view datum).1,
            (view datum).2)
          (circuit datum).1 ⟨1, one_ne_zero⟩ witnessTape.inputMacKey)).map loggedOutcome))
          (result, log) =
      ((((adversary.chooseInput parameter (circuit datum) auxiliary).run idealOracle
        (firstState (view datum) (circuit datum).1 ⟨1, one_ne_zero⟩
          witnessTape.inputMacKey)).map loggedOutcome)) (result, log)
    exact run_idealOracle_agree (adversary.chooseInput parameter (circuit datum) auxiliary)
      (UsedBad (view datum).1 (values datum) key)
      (firstState (programIndices (usedPrograms key (values datum)) (view datum).1,
          (view datum).2) (circuit datum).1 ⟨1, one_ne_zero⟩ witnessTape.inputMacKey)
      (firstState (view datum) (circuit datum).1 ⟨1, one_ne_zero⟩ witnessTape.inputMacKey) rfl
      (fun query notBad =>
        publicAnswer_usedPrograms (view datum).1 (view datum).2 key (values datum) query notBad)
      result log goodQuery
  · have badLe := firstStage_hidden_le data view circuit (fun datum => (circuit datum).1)
      carrier adversary parameter auxiliary queryLabelIndex
      (fun datum => usedHidden (view datum).1 (values datum)) 2
      (fun datum query => usedHidden_card _ _ query)
    have transport :
        (((PMF.uniformOfFintype InputMacKey).bind fun key => data.bind fun datum =>
            ((adversary.chooseInput parameter (circuit datum) auxiliary).run idealOracle
              (firstState (view datum) (circuit datum).1 (carrier datum) key)).map
                fun selected => (key, datum, selected)).map
          fun triple => ((triple.1, triple.2.1), loggedOutcome triple.2.2)) =
        jointLaw ((PMF.uniformOfFintype InputMacKey).bind fun key =>
            data.map fun datum => (key, datum))
          fun sample => loggedFirstStage adversary parameter auxiliary (circuit sample.2)
            (view sample.2) := by
      unfold jointLaw
      rw [bind_pairLaw data fun sample =>
        (loggedFirstStage adversary parameter auxiliary (circuit sample.2)
          (view sample.2)).map (Prod.mk sample), PMF.map_bind]
      refine congrArg (PMF.bind _) (funext fun key => ?_)
      rw [PMF.map_bind]
      refine congrArg (PMF.bind data) (funext fun datum => ?_)
      rw [← map_loggedOutcome_firstState adversary parameter auxiliary (circuit datum)
        (view datum) (circuit datum).1 (carrier datum) key, PMF.map_comp, PMF.map_comp]
      rfl
    rw [← transport, PMF.toOuterMeasure_map_apply]
    refine le_trans (ENNReal.toReal_mono (by finiteness) (le_trans (le_of_eq ?_) badLe)) ?_
    · rfl
    · exact le_of_eq (toReal_two_budget _)

/-! ### The second oracle hop: the second stage keeps only the selected programming -/

/-- Two views answer a query identically when they agree at the query's own index. -/
theorem publicAnswer_permutation_congr (first second : PermutationOracle FixedKeyIndex Block)
    (rest : PermutationOracle Garbling.EncIndex Block × (BaseField → Block × Block))
    (query : Query)
    (forward : ∀ index value, query = .fixedForward index value →
      first.permutation index value = second.permutation index value)
    (inverse : ∀ index value, query = .fixedInverse index value →
      (first.permutation index).symm value = (second.permutation index).symm value) :
    publicAnswer (first, rest) query = publicAnswer (second, rest) query := by
  cases query with
  | fixedForward index value => exact forward index value rfl
  | fixedInverse index value => exact inverse index value rfl
  | encForward _ _ => rfl
  | encInverse _ _ => rfl
  | hash _ => rfl

/-- Programming reads one index only through its own request. -/
theorem programIndices_congr_at (first second : Programs)
    (oracle : PermutationOracle FixedKeyIndex Block) (index : FixedKeyIndex)
    (same : first index = second index) :
    (programIndices first oracle).permutation index =
      (programIndices second oracle).permutation index := by
  simp only [programIndices, same]

/-! ### The reference coordinates of the fresh secrets -/

/-- The reference sample the fresh digests and pads name. -/
def digestedRaw (mask r1 r2 : BaseField) (digests : GateValues (BitVec 384))
    (pads : GateValues BitAdaptor.Ciphertext) : Coordinates :=
  ⟨mask, r1, r2, digestField digests, pads⟩

theorem tableRow_digested (bridgeKey mask r1 r2 : BaseField) (key : InputMacKey)
    (digests : GateValues (BitVec 384)) (pads : GateValues BitAdaptor.Ciphertext)
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount) :
    tableRow (Coordinates.table bridgeKey key (digestedRaw mask r1 r2 digests pads))
        adaptor position =
      pads adaptor position ^^^ BitAdaptor.fieldBytes
        ((digestedRaw mask r1 r2 digests pads).slope adaptor +
          digestField digests adaptor position) := by
  unfold tableRow
  rw [Coordinates.table_rows]
  rfl

theorem selectOutput_true (input : AffineInput) (raw : Coordinates) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) (bit : inputBits input adaptor position = true) :
    (encodeCoordinates input raw).hash adaptor position =
      raw.slope adaptor + raw.hash adaptor position := by
  simp only [encodeCoordinates, selectOutput, bit, if_true]

/-- At a gate whose slot reads the selected label, the reference game's programming is the
first hop's programming. -/
theorem selectedPrograms_selected (key : InputMacKey) (input : AffineInput)
    (bridgeKey mask r1 r2 : BaseField) (digests : GateValues (BitVec 384))
    (pads : GateValues BitAdaptor.Ciphertext) (index : FixedKeyIndex)
    (selected : slotBit index.slot = inputBits input index.adaptor index.position) :
    selectedPrograms key input
        (encodeCoordinates input (digestedRaw mask r1 r2 digests pads)).hash
        (tableRow (Coordinates.table bridgeKey key (digestedRaw mask r1 r2 digests pads)))
        digests index =
      usedPrograms key (freshValue digests pads) index := by
  obtain ⟨adaptor, position, slot⟩ := index
  cases slot with
  | hash chunk =>
    have bit : inputBits input adaptor position = false := selected.symm
    rw [selectedPrograms_hash, bit, if_neg (by simp)]
    simp only [usedPrograms, usedLabel, freshValue, selectedLabel, slotRange, bit,
      BitAdaptor.encode, if_neg (by simp : ¬(false = true))]
  | pad chunk =>
    have bit : inputBits input adaptor position = true := selected.symm
    rw [selectedPrograms_pad, bit, if_pos rfl]
    have row : tableRow (Coordinates.table bridgeKey key (digestedRaw mask r1 r2 digests pads))
          adaptor position ^^^ BitAdaptor.fieldBytes
            ((encodeCoordinates input (digestedRaw mask r1 r2 digests pads)).hash adaptor
              position) = pads adaptor position := by
      rw [tableRow_digested, selectOutput_true input _ adaptor position bit]
      exact xor_xor_cancel _ _
    rw [row]
    simp [usedPrograms, usedLabel, freshValue, selectedLabel, slotRange, bit,
      BitAdaptor.encode]

/-- At a gate whose slot reads the unselected label, the reference game programs nothing. -/
theorem selectedPrograms_unselected (key : InputMacKey) (input : AffineInput)
    (outputs : GateValues BaseField) (rows : GateValues BitAdaptor.Ciphertext)
    (fibers : GateValues (BitVec 384)) (index : FixedKeyIndex)
    (unselected : slotBit index.slot ≠ inputBits input index.adaptor index.position) :
    selectedPrograms key input outputs rows fibers index = none := by
  obtain ⟨adaptor, position, slot⟩ := index
  cases slot with
  | hash chunk =>
    have bit : inputBits input adaptor position = true := by
      revert unselected
      cases inputBits input adaptor position <;> simp [slotBit]
    rw [selectedPrograms_hash, bit, if_pos rfl]
  | pad chunk =>
    have bit : inputBits input adaptor position = false := by
      revert unselected
      cases inputBits input adaptor position <;> simp [slotBit]
    rw [selectedPrograms_pad, bit, if_neg (by simp)]

/-- The label coordinate a query names when its own slot reads the label the input leaves
unselected. Every other query sees the same programming in both views. -/
def unreadQueryIndex (input : AffineInput) (query : Query) : Option LabelIndex :=
  match queryIndex query with
  | none => none
  | some index =>
    if slotBit index.slot = unreadLabelBits input (adaptorCoordinate index.adaptor, index.position)
      then some (adaptorCoordinate index.adaptor, index.position) else none

/-- A query is bad for the second oracle hop when the unselected label of its own gate is
one of its hidden label values. -/
def SelectedBad (oracle : PermutationOracle FixedKeyIndex Block)
    (values : FixedKeyIndex → Block) (key : InputMacKey) (input : AffineInput)
    (query : Query) : Prop :=
  ∃ index, unreadQueryIndex input query = some index ∧
    keyLabel key index.1 index.2 (unreadLabelBits input index) ∈ usedHidden oracle values query

/-- A slot that does not read the selected label reads the unselected one. -/
theorem slotBit_eq_unread (input : AffineInput) (index : FixedKeyIndex)
    (unselected : slotBit index.slot ≠ inputBits input index.adaptor index.position) :
    slotBit index.slot =
      unreadLabelBits input (adaptorCoordinate index.adaptor, index.position) := by
  rw [unreadLabelBits, ← inputBits_eq]
  revert unselected
  cases slotBit index.slot <;> cases inputBits input index.adaptor index.position <;> simp

/-- Off its bad label values, a query cannot tell the first hop's programming at every used
label from the reference game's programming at the selected labels only. -/
theorem publicAnswer_selectedPrograms (oracle : PermutationOracle FixedKeyIndex Block)
    (rest : PermutationOracle Garbling.EncIndex Block × (BaseField → Block × Block))
    (key : InputMacKey) (input : AffineInput) (bridgeKey mask r1 r2 : BaseField)
    (digests : GateValues (BitVec 384)) (pads : GateValues BitAdaptor.Ciphertext)
    (query : Query)
    (good : ¬ SelectedBad oracle (freshValue digests pads) key input query) :
    publicAnswer (programIndices (usedPrograms key (freshValue digests pads)) oracle, rest)
        query =
      publicAnswer (programIndices (selectedPrograms key input
        (encodeCoordinates input (digestedRaw mask r1 r2 digests pads)).hash
        (tableRow (Coordinates.table bridgeKey key (digestedRaw mask r1 r2 digests pads)))
        digests) oracle, rest) query := by
  have atIndex (index : FixedKeyIndex) (named : queryIndex query = some index) :
      (programIndices (usedPrograms key (freshValue digests pads)) oracle).permutation index =
        (programIndices (selectedPrograms key input
          (encodeCoordinates input (digestedRaw mask r1 r2 digests pads)).hash
          (tableRow (Coordinates.table bridgeKey key (digestedRaw mask r1 r2 digests pads)))
          digests) oracle).permutation index ∨
        (usedLabel key index ∉ usedHidden oracle (freshValue digests pads) query ∧
          (programIndices (usedPrograms key (freshValue digests pads)) oracle).permutation index =
            programmed (oracle.permutation index) (usedLabel key index)
              (freshValue digests pads index ^^^ usedLabel key index) ∧
          (programIndices (selectedPrograms key input
            (encodeCoordinates input (digestedRaw mask r1 r2 digests pads)).hash
            (tableRow (Coordinates.table bridgeKey key (digestedRaw mask r1 r2 digests pads)))
            digests) oracle).permutation index = oracle.permutation index) := by
    by_cases selected : slotBit index.slot = inputBits input index.adaptor index.position
    · exact Or.inl (programIndices_congr_at _ _ oracle index
        (selectedPrograms_selected key input bridgeKey mask r1 r2 digests pads index
          selected).symm)
    · have unread : unreadQueryIndex input query =
          some (adaptorCoordinate index.adaptor, index.position) := by
        rw [unreadQueryIndex, named]
        exact if_pos (slotBit_eq_unread input index selected)
      have missing : usedLabel key index ∉ usedHidden oracle (freshValue digests pads) query := by
        rw [usedLabel_eq_keyLabel, slotBit_eq_unread input index selected]
        intro member
        exact good ⟨(adaptorCoordinate index.adaptor, index.position), unread, member⟩
      exact Or.inr ⟨missing,
        programIndices_eq_programmed _ oracle index _ _ rfl,
        programIndices_none _ oracle index
          (selectedPrograms_unselected key input _ _ digests index selected)⟩
  refine publicAnswer_permutation_congr _ _ rest query ?_ ?_
  · rintro index value rfl
    rcases atIndex index rfl with same | ⟨missing, first, second⟩
    · rw [same]
    · rw [first, second]
      exact programmed_apply_of_not_mem _ _ _ _ missing
  · rintro index value rfl
    rcases atIndex index rfl with same | ⟨missing, first, second⟩
    · rw [same]
    · rw [first, second]
      exact programmed_symm_apply_of_not_mem _ _ _ _ missing

end

end Kriterion.ArgoMAC.Security
