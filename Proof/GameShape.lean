/-
This file puts the two privacy games into the shape the chain of games needs
and discharges the `unread` hypothesis of the second-stage bad bound.

The second-stage bound defers the label of every gate that the run never reads.
Three facts make that deferral legitimate. The reference table is built from
secret oracles that discard their label argument, so it does not depend on the
label key at all. The first stage runs on the ideal oracle, which reads only
the view and the log, so it never touches the key. The second stage reads the
key only through the selected labels: the honest labels handed to the
adversary, the label the simulator steers at, and the labels the reference game
programs are all `selectedLabel`. Replacing every gate's unselected label
therefore changes none of the three games.
-/

import Proof.SecondStage
import Proof.FreshBridge

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit

noncomputable section

/-! ### The labels one input selects -/

/-- The coordinate a label index names: `false` is the x coordinate, `true` the y. -/
def inputCoordinate (input : AffineInput) : Bool → BaseField
  | false => input.x
  | true => input.y

/-- The bit an input selects at one label index. -/
def inputLabelBits (input : AffineInput) : LabelIndex → Bool :=
  fun index => coordinateValues (inputCoordinate input index.1) index.2

/-- The label an input leaves unread at one label index. -/
def unreadLabelBits (input : AffineInput) : LabelIndex → Bool :=
  fun index => !inputLabelBits input index

theorem inputBits_eq (input : AffineInput) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) :
    inputBits input adaptor position =
      inputLabelBits input (adaptorCoordinate adaptor, position) := by
  cases adaptor <;> rfl

theorem unreadLabelBits_ne (input : AffineInput) (index : LabelIndex) :
    unreadLabelBits input index ≠ inputLabelBits input index :=
  Bool.not_ne_self _

/-- Replacing the other label of a pair leaves the selected label alone. -/
theorem encode_setPairLabel_of_ne (pair : BitAdaptor.Key) (value other : Bool) (label : Block)
    (different : other ≠ value) :
    BitAdaptor.encode (setPairLabel pair other label) value = BitAdaptor.encode pair value := by
  cases value <;> cases other <;> first
    | exact absurd rfl different
    | rfl

/-- Replacing one label of every gate leaves every other label alone. -/
theorem keyLabel_setKeyLabels_of_ne (key : InputMacKey) (values : LabelIndex → Bool)
    (labels : LabelIndex → Block) (index : LabelIndex) (value : Bool)
    (different : values index ≠ value) :
    keyLabel (setKeyLabels key values labels) index.1 index.2 value =
      keyLabel key index.1 index.2 value := by
  unfold keyLabel
  rw [coordinateKey_setKeyLabels, get_setCoordinateLabels]
  exact encode_setPairLabel_of_ne _ _ _ _ different

/-- The selected label of a gate does not see the replaced labels. -/
theorem selectedLabel_setKeyLabels (key : InputMacKey) (input : AffineInput)
    (labels : LabelIndex → Block) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) :
    selectedLabel (setKeyLabels key (unreadLabelBits input) labels) input adaptor position =
      selectedLabel key input adaptor position := by
  rw [selectedLabel_eq, selectedLabel_eq, inputBits_eq]
  exact keyLabel_setKeyLabels_of_ne key (unreadLabelBits input) labels
    (adaptorCoordinate adaptor, position) _ (unreadLabelBits_ne input _)

/-- One coordinate's encoding does not see the replaced labels. -/
theorem encodeCoordinate_setCoordinateLabels (key : CoordinateMacKey)
    (values : Fin coordinateBitCount → Bool) (labels : Fin coordinateBitCount → Block)
    (bits : BitVec coordinateBitCount)
    (different : ∀ position, values position ≠ bits.getLsb position) :
    encodeCoordinate (setCoordinateLabels key values labels) bits = encodeCoordinate key bits := by
  refine Vector.ext fun position member => ?_
  simp only [encodeCoordinate, Vector.getElem_ofFn]
  rw [show (setCoordinateLabels key values labels)[position] =
      (setCoordinateLabels key values labels).get ⟨position, member⟩ from rfl,
    show key[position] = key.get ⟨position, member⟩ from rfl, get_setCoordinateLabels]
  exact encode_setPairLabel_of_ne _ _ _ _ (different ⟨position, member⟩)

/-- The honest labels of an input do not see the replaced labels. -/
theorem encodeAffine_setKeyLabels (key : InputMacKey) (input : AffineInput)
    (labels : LabelIndex → Block) :
    (setKeyLabels key (unreadLabelBits input) labels).encodeAffine input =
      key.encodeAffine input := by
  have coordinate (side : Bool) :
      encodeCoordinate (setCoordinateLabels (coordinateKey key side)
          (fun position => unreadLabelBits input (side, position))
          (fun position => labels (side, position)))
          (coordinateBits (inputCoordinate input side)) =
        encodeCoordinate (coordinateKey key side)
          (coordinateBits (inputCoordinate input side)) :=
    encodeCoordinate_setCoordinateLabels _ _ _ _ fun position =>
      unreadLabelBits_ne input (side, position)
  exact congrArg₂ InputMac.mk (coordinate false) (coordinate true)

/-! ### The reference table ignores the label key -/

/-- One secret gate's garbling ignores its label pair. -/
theorem garble_secretOracle_key (hash : BaseField) (pad : BitAdaptor.Ciphertext)
    (slope : BaseField) (first second : BitAdaptor.Key) :
    BitAdaptor.garble (secretOracle hash pad) slope first =
      BitAdaptor.garble (secretOracle hash pad) slope second := rfl

/-- One secret adaptor's garbling ignores its coordinate key. -/
theorem garble_secretWindows_key (hash : GateValues BaseField)
    (pad : GateValues BitAdaptor.Ciphertext) (adaptor : CurveAdaptor) (slope : BaseField)
    (keys : CoordinateMacKey) :
    DigitAdaptor.garble (secretWindows hash pad adaptor) slope keys =
      DigitAdaptor.garble (secretWindows hash pad adaptor) slope
        (Vector.replicate coordinateBitCount ⟨0, 1⟩) := by
  have same : (Vector.ofFn fun index : Fin coordinateBitCount =>
        BitAdaptor.garble (secretWindows hash pad adaptor index.val) slope (keys.get index)) =
      Vector.ofFn fun index : Fin coordinateBitCount =>
        BitAdaptor.garble (secretWindows hash pad adaptor index.val) slope
          ((Vector.replicate coordinateBitCount (⟨0, 1⟩ : BitAdaptor.Key)).get index) := by
    refine congrArg Vector.ofFn (funext fun index => ?_)
    rw [secretWindows_val]
    exact garble_secretOracle_key _ _ _ _ _
  simp only [DigitAdaptor.garble, same]

/-- The reference table does not depend on the label key: the secret oracles discard
their label argument. -/
theorem Coordinates.table_key (bridgeKey : BaseField) (raw : Coordinates)
    (first second : InputMacKey) :
    raw.table bridgeKey first = raw.table bridgeKey second := by
  simp only [Coordinates.table, CurveMembership.garble, secretOracles, garble_secretWindows_key]

/-! ### The first stage never touches the key -/

/-- An ideal-oracle run's result law depends on the state only through the view and
the log. -/
theorem map_fst_run_congr {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget)
    (first second : State) (sameView : first.view = second.view)
    (sameLog : first.log = second.log) :
    (program.run idealOracle first).map Prod.fst =
      (program.run idealOracle second).map Prod.fst := by
  have logged := map_loggedOutcome_congr program first second sameView sameLog
  have project (state : State) : (program.run idealOracle state).map Prod.fst =
      ((program.run idealOracle state).map loggedOutcome).map Prod.fst := by
    rw [PMF.map_comp]
    rfl
  rw [project first, project second, logged]

/-- The first stage of a game does not read the label key. -/
theorem firstStage_key_congr (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (circuit : Garbling.Public) (view : View) (table : CurveMembership.Table)
    (carrier : NonZeroBase) (first second : InputMacKey) :
    ((adversary.chooseInput parameter circuit auxiliary).run idealOracle
        (firstState view table carrier first)).map loggedOutcome =
      ((adversary.chooseInput parameter circuit auxiliary).run idealOracle
        (firstState view table carrier second)).map loggedOutcome := by
  rw [map_loggedOutcome_firstState adversary parameter auxiliary circuit view table carrier first,
    map_loggedOutcome_firstState adversary parameter auxiliary circuit view table carrier second]

/-! ### Programming reads only the view and the log -/

theorem programIfFresh_view_congr (first second : State) (sameView : first.view = second.view)
    (sameLog : first.log = second.log) (request : ProgramRequest) :
    (programIfFresh first request).view = (programIfFresh second request).view := by
  have same : request.Fresh first.log first.view.1 ↔ request.Fresh second.log second.view.1 := by
    rw [sameLog, sameView]
  unfold programIfFresh
  by_cases fresh : request.Fresh first.log first.view.1
  · rw [if_pos fresh, if_pos (same.mp fresh)]
    simp only [sameView]
  · rw [if_neg fresh, if_neg fun other => fresh (same.mpr other)]
    exact sameView

theorem programAll_view_congr (first second : State) (sameView : first.view = second.view)
    (sameLog : first.log = second.log) (requests : List ProgramRequest) :
    (programAll first requests).view = (programAll second requests).view := by
  induction requests generalizing first second with
  | nil => exact sameView
  | cons request rest inductionHypothesis =>
    rw [programAll_cons, programAll_cons]
    exact inductionHypothesis _ _ (programIfFresh_view_congr first second sameView sameLog request)
      (by rw [programIfFresh_log, programIfFresh_log, sameLog])

/-! ### The steering requests -/

/-- The steering requests as a law of their own: the simulator's steering is this law
followed by the programming of the state. It reads the state only through the view and
the table. -/
def steerRequestLaw (view : View) (table : CurveMembership.Table) (input : AffineInput)
    (mac : InputMac) (target : BaseField) : PMF (List ProgramRequest) :=
  let bit := steeringBit input
  let label := mac.x.get 0
  let row := table.x7.get 0
  let current := CurveMembership.evaluate (curveOracles view.1) table input mac
  let position := BitAdaptor.evaluate (fixedKeyGate view.1 .x7 0) row bit label
  let wanted := position + (target - current)
  if bit then PMF.pure (padRequests label (BitAdaptor.fieldBytes wanted ^^^ row.trueRow))
  else (uniformHashFiber wanted).map (hashRequests label)

/-- Steering is the steering-request law followed by the programming. -/
theorem steer_eq_map (state : State) (input : AffineInput) (mac : InputMac)
    (target : BaseField) :
    steer state input mac target =
      (steerRequestLaw state.view state.table input mac target).map (programAll state) := by
  unfold steer steerRequestLaw
  simp only
  split
  · rw [PMF.pure_map]
  · rw [PMF.map_comp]
    rfl

/-- The steering law reads the state only through the view and the table. -/
theorem steer_visible_congr (first second : State) (sameView : first.view = second.view)
    (sameLog : first.log = second.log) (sameTable : first.table = second.table)
    (input : AffineInput) (mac : InputMac) (target : BaseField) :
    (steer first input mac target).map (fun state => (state.view, state.log)) =
      (steer second input mac target).map (fun state => (state.view, state.log)) := by
  rw [steer_eq_map, steer_eq_map, PMF.map_comp, PMF.map_comp, sameView, sameTable]
  refine congrArg (fun step => PMF.map step (steerRequestLaw second.view second.table input mac
    target)) (funext fun requests => ?_)
  exact Prod.ext (programAll_view_congr first second sameView sameLog requests)
    (show (programAll first requests).log = (programAll second requests).log by
      rw [programAll_log, programAll_log, sameLog])

/-! ### The three second stages and the labels they never read -/

/-- The state a second stage starts from: the view and the log left by the first stage,
the public data, and the label key. -/
def stageTwoState (view : View) (priorLog : List Query) (table : CurveMembership.Table)
    (carrier : NonZeroBase) (key : InputMacKey) : State :=
  { view, log := priorLog, table, carrier, inputMacKey := key }

theorem stageTwoState_view (view : View) (priorLog : List Query)
    (table : CurveMembership.Table) (carrier : NonZeroBase) (key : InputMacKey) :
    (stageTwoState view priorLog table carrier key).view = view := rfl

theorem stageTwoState_log (view : View) (priorLog : List Query)
    (table : CurveMembership.Table) (carrier : NonZeroBase) (key : InputMacKey) :
    (stageTwoState view priorLog table carrier key).log = priorLog := rfl

theorem stageTwoState_table (view : View) (priorLog : List Query)
    (table : CurveMembership.Table) (carrier : NonZeroBase) (key : InputMacKey) :
    (stageTwoState view priorLog table carrier key).table = table := rfl

theorem stageTwoState_carrier (view : View) (priorLog : List Query)
    (table : CurveMembership.Table) (carrier : NonZeroBase) (key : InputMacKey) :
    (stageTwoState view priorLog table carrier key).carrier = carrier := rfl

theorem stageTwoState_inputMacKey (view : View) (priorLog : List Query)
    (table : CurveMembership.Table) (carrier : NonZeroBase) (key : InputMacKey) :
    (stageTwoState view priorLog table carrier key).inputMacKey = key := rfl

/-- The decision run in logged form. It reads its state only through the view and the
log, so a second stage may hand it the visible data alone. -/
def decisionLaw (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (circuit : Garbling.Public) (advState : adversary.State)
    (data : LamportSignature × View × List Query) : PMF (Bool × List Query) :=
  ((adversary.decide parameter circuit data.1 auxiliary advState).run idealOracle
    (stageTwoState data.2.1 data.2.2 circuit.1 ⟨1, one_ne_zero⟩
      witnessTape.inputMacKey)).map loggedOutcome

/-- Every logged decision run factors through the visible data of its state. -/
theorem bind_decisionLaw (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (circuit : Garbling.Public) (advState : adversary.State)
    (law : PMF (LamportSignature × State)) :
    (law.bind fun encoded =>
        ((adversary.decide parameter circuit encoded.1 auxiliary advState).run idealOracle
          encoded.2).map loggedOutcome) =
      (law.map fun encoded => (encoded.1, encoded.2.view, encoded.2.log)).bind
        (decisionLaw adversary parameter auxiliary circuit advState) := by
  rw [PMF.bind_map]
  refine congrArg (PMF.bind law) (funext fun encoded => ?_)
  exact map_loggedOutcome_congr _ _ _ rfl rfl

/-- The hybrid second stage: the honest labels of the state's key on the unprogrammed
view. -/
def hybridStageTwo (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (circuit : Garbling.Public) (input : AffineInput) (advState : adversary.State)
    (state : State) : PMF (Bool × List Query) :=
  ((adversary.decide parameter circuit
      (Lamport.selectedLabels (state.inputMacKey.encodeAffine input)) auxiliary advState).run
    idealOracle state).map loggedOutcome

/-- The hybrid second stage never reads the labels the input leaves unselected. -/
theorem hybridStageTwo_unread (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (circuit : Garbling.Public) (input : AffineInput) (advState : adversary.State)
    (view : View) (priorLog : List Query) (table : CurveMembership.Table)
    (carrier : NonZeroBase) (key : InputMacKey) (labels : LabelIndex → Block) :
    hybridStageTwo adversary parameter auxiliary circuit input advState
        (stageTwoState view priorLog table carrier
          (setKeyLabels key (unreadLabelBits input) labels)) =
      hybridStageTwo adversary parameter auxiliary circuit input advState
        (stageTwoState view priorLog table carrier key) := by
  unfold hybridStageTwo
  simp only [stageTwoState_inputMacKey, encodeAffine_setKeyLabels]
  exact map_loggedOutcome_congr _ _ _
    (by rw [stageTwoState_view, stageTwoState_view]) (by rw [stageTwoState_log, stageTwoState_log])

/-- The reference programs touch only the selected label of each gate. -/
theorem selectedPrograms_setKeyLabels (key : InputMacKey) (input : AffineInput)
    (blocks : LabelIndex → Block) (outputs : GateValues BaseField)
    (rows : GateValues BitAdaptor.Ciphertext) (fibers : GateValues (BitVec 384)) :
    selectedPrograms (setKeyLabels key (unreadLabelBits input) blocks) input outputs rows
        fibers = selectedPrograms key input outputs rows fibers := by
  funext index
  simp only [selectedPrograms, selectedLabel_setKeyLabels]

/-- The reference second stage: sample the fibers, program the selected labels, and run
the decision on the honest labels. -/
def referenceStageTwo (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (circuit : Garbling.Public) (input : AffineInput) (advState : adversary.State)
    (outputs : GateValues BaseField) (state : State) : PMF (Bool × List Query) :=
  (uniformHashFibers outputs).bind fun fibers =>
    ((adversary.decide parameter circuit
        (Lamport.selectedLabels (state.inputMacKey.encodeAffine input)) auxiliary advState).run
      idealOracle (programSelected state input outputs fibers)).map loggedOutcome

/-- The reference second stage never reads the labels the input leaves unselected. -/
theorem referenceStageTwo_unread (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (circuit : Garbling.Public) (input : AffineInput) (advState : adversary.State)
    (outputs : GateValues BaseField) (view : View) (priorLog : List Query)
    (table : CurveMembership.Table) (carrier : NonZeroBase) (key : InputMacKey)
    (blocks : LabelIndex → Block) :
    referenceStageTwo adversary parameter auxiliary circuit input advState outputs
        (stageTwoState view priorLog table carrier
          (setKeyLabels key (unreadLabelBits input) blocks)) =
      referenceStageTwo adversary parameter auxiliary circuit input advState outputs
        (stageTwoState view priorLog table carrier key) := by
  unfold referenceStageTwo
  refine congrArg (PMF.bind (uniformHashFibers outputs)) (funext fun fibers => ?_)
  simp only [stageTwoState_inputMacKey, encodeAffine_setKeyLabels]
  refine map_loggedOutcome_congr _ _ _ ?_
    (by rw [programSelected_log, programSelected_log, stageTwoState_log, stageTwoState_log])
  unfold programSelected
  simp only [stageTwoState_view, stageTwoState_table, stageTwoState_inputMacKey,
    selectedPrograms_setKeyLabels]

/-- The simulated second stage: the simulator's labels and steering, then the decision. -/
def simulatedStageTwo [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (circuit : Garbling.Public) (input : AffineInput)
    (output : Option Point) (advState : adversary.State) (state : State) :
    PMF (Bool × List Query) :=
  (simulateEncode state input output).bind fun encoded =>
    ((adversary.decide parameter circuit encoded.1 auxiliary advState).run idealOracle
      encoded.2).map loggedOutcome

/-- The simulated encoding reads the state only through the view, the log, the table, the
carrier and the honest labels of the chosen input. -/
theorem simulateEncode_visible_congr [FieldCertificate] [GroupCertificate]
    (first second : State) (sameView : first.view = second.view)
    (sameLog : first.log = second.log) (sameTable : first.table = second.table)
    (sameCarrier : first.carrier = second.carrier) (input : AffineInput)
    (output : Option Point)
    (sameMac : first.inputMacKey.encodeAffine input = second.inputMacKey.encodeAffine input) :
    (simulateEncode first input output).map
        (fun encoded => (encoded.1, encoded.2.view, encoded.2.log)) =
      (simulateEncode second input output).map
        (fun encoded => (encoded.1, encoded.2.view, encoded.2.log)) := by
  have steered (state : State) (signature : LamportSignature) (mac : InputMac)
      (target : BaseField) :
      (((steer state input mac target).map fun next => (signature, next)).map
          fun encoded => (encoded.1, encoded.2.view, encoded.2.log)) =
        ((steer state input mac target).map fun next => (next.view, next.log)).map
          fun visible => (signature, visible) := by
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  unfold simulateEncode
  simp only [sameMac, sameCarrier]
  split
  · rw [PMF.pure_map, PMF.pure_map, sameView, sameLog]
  · rw [steered, steered,
      steer_visible_congr first second sameView sameLog sameTable input _ _]

/-- The simulated second stage never reads the labels the input leaves unselected. -/
theorem simulatedStageTwo_unread [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (circuit : Garbling.Public) (input : AffineInput)
    (output : Option Point) (advState : adversary.State) (view : View) (priorLog : List Query)
    (table : CurveMembership.Table) (carrier : NonZeroBase) (key : InputMacKey)
    (blocks : LabelIndex → Block) :
    simulatedStageTwo adversary parameter auxiliary circuit input output advState
        (stageTwoState view priorLog table carrier
          (setKeyLabels key (unreadLabelBits input) blocks)) =
      simulatedStageTwo adversary parameter auxiliary circuit input output advState
        (stageTwoState view priorLog table carrier key) := by
  unfold simulatedStageTwo
  rw [bind_decisionLaw, bind_decisionLaw]
  have visible := simulateEncode_visible_congr
    (stageTwoState view priorLog table carrier (setKeyLabels key (unreadLabelBits input) blocks))
    (stageTwoState view priorLog table carrier key)
    (by rw [stageTwoState_view, stageTwoState_view])
    (by rw [stageTwoState_log, stageTwoState_log])
    (by rw [stageTwoState_table, stageTwoState_table])
    (by rw [stageTwoState_carrier, stageTwoState_carrier]) input output
    (by rw [stageTwoState_inputMacKey, stageTwoState_inputMacKey,
      encodeAffine_setKeyLabels])
  rw [visible]

/-! ### The unused curve coordinates of the tape -/

/-- The tape with its curve coordinates replaced. The reference game samples them
separately, so the tape's own copies are marginalised away. -/
def setCurve (tape : Garbling.Randomness) (curve : NonZeroBase × BaseField × BaseField) :
    Garbling.Randomness :=
  { tape with curveMask := curve.1, curveR1 := curve.2.1, curveR2 := curve.2.2 }

/-- Exchanging a tape's curve coordinates with a separate sample is an involution. -/
def swapCurve : Garbling.Randomness × (NonZeroBase × BaseField × BaseField) ≃
    Garbling.Randomness × (NonZeroBase × BaseField × BaseField) where
  toFun pair := (setCurve pair.1 pair.2, (pair.1.curveMask, pair.1.curveR1, pair.1.curveR2))
  invFun pair := (setCurve pair.1 pair.2, (pair.1.curveMask, pair.1.curveR1, pair.1.curveR2))
  left_inv pair := by
    obtain ⟨tape, _⟩ := pair
    cases tape
    rfl
  right_inv pair := by
    obtain ⟨tape, _⟩ := pair
    cases tape
    rfl

/-- A uniform tape with fresh uniform curve coordinates is a uniform tape. -/
theorem uniform_bind_setCurve {Outcome : Type} (continuation : Garbling.Randomness → PMF Outcome) :
    ((PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype (NonZeroBase × BaseField × BaseField)).bind fun curve =>
          continuation (setCurve tape curve)) =
      (PMF.uniformOfFintype Garbling.Randomness).bind continuation := by
  rw [uniformOfFintype_bind_prod]
  have swapped := uniformOfFintype_bind_equiv swapCurve
    fun pair : Garbling.Randomness × (NonZeroBase × BaseField × BaseField) => continuation pair.1
  simp only [swapCurve, Equiv.coe_fn_mk] at swapped
  have unprod : ((PMF.uniformOfFintype
        (Garbling.Randomness × (NonZeroBase × BaseField × BaseField))).bind fun pair =>
      continuation pair.1) =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype (NonZeroBase × BaseField × BaseField)).bind fun _ =>
          continuation tape :=
    (uniformOfFintype_bind_prod
      fun tape (_ : NonZeroBase × BaseField × BaseField) => continuation tape).symm
  rw [swapped, unprod]
  simp only [PMF.bind_const]

/-! ### The simulated game in two-stage shape -/

theorem map_fst_loggedOutcome {Result : Type} (law : PMF (Result × State)) :
    (law.map loggedOutcome).map Prod.fst = law.map Prod.fst := by
  rw [PMF.map_comp]
  rfl

/-- The simulated game: a uniform tape and a uniform carrier, the first stage on the
unprogrammed view, and the simulated second stage. -/
theorem simulatedGame_eq [FieldCertificate] [GroupCertificate] (bytes : Nat)
    (adversary : Adversary) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    idealGame Garbling.garbledCircuit (fun _ => bytes) simulator idealOracle adversary parameter
        scalar auxiliary =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
          ((adversary.chooseInput parameter (curveTable tape, carrierBits carrier) auxiliary).run
              idealOracle (initialState tape (curveTable tape) carrier)).bind fun selected =>
            (simulatedStageTwo adversary parameter auxiliary
              (curveTable tape, carrierBits carrier) selected.1.1
              (checkedScalarMultiplication scalar.value selected.1.1) selected.1.2
              selected.2).map Prod.fst := by
  unfold idealGame simulator simulateGarble simulatedStageTwo
  simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind, Function.comp_def, map_fst_loggedOutcome]
  rfl

end

end Kriterion.ArgoMAC.Security
