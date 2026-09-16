/-
This file walks the simulated game to the reference game of the tape's own
bridge key, with the steering still in place.

The simulated game garbles the real curve table for the tape's bridge key `u`
and runs both adversary stages on the tape's own fixed-key oracle; its second
stage hands over the honest labels and then steers the steering gate. The three
hops of the hybrid side apply again. The oracle is reparametrised, so the real
table becomes the reference table of fresh per-gate digests and pads; the first
stage moves to the unprogrammed oracle; and the second stage keeps only the
programming at the selected labels. The last hop is the one the steering
complicates: the steering reads the released value and the steering gate at the
*selected* labels only, so the two views it can run on produce the same request
list, and programming that list preserves the agreement of the two views off
the unselected labels.
-/

import Proof.HybridReference

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

/-! ### Evaluation reads only the selected labels -/

/-- Two oracles that agree at a label on a gate's hash slots produce the same digest. -/
theorem hashBytes_congr (first second : PermutationOracle FixedKeyIndex Block)
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount) (label : Block)
    (agree : ∀ chunk : Fin 3,
      first.permutation ⟨adaptor, position, .hash chunk⟩ label =
        second.permutation ⟨adaptor, position, .hash chunk⟩ label) :
    BitAdaptor.hashBytes (fixedKeyPermutations first adaptor position.val) label =
      BitAdaptor.hashBytes (fixedKeyPermutations second adaptor position.val) label := by
  simp only [BitAdaptor.hashBytes, fixedKeyPermutations_val, daviesMeyer, Cryptography.xor, agree]

/-- Two oracles that agree at a label on a gate's pad slots produce the same pad. -/
theorem padBytes_congr (first second : PermutationOracle FixedKeyIndex Block)
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount) (label : Block)
    (agree : ∀ chunk : Fin 2,
      first.permutation ⟨adaptor, position, .pad chunk⟩ label =
        second.permutation ⟨adaptor, position, .pad chunk⟩ label) :
    BitAdaptor.padBytes (fixedKeyPermutations first adaptor position.val) label =
      BitAdaptor.padBytes (fixedKeyPermutations second adaptor position.val) label := by
  simp only [BitAdaptor.padBytes, fixedKeyPermutations_val, daviesMeyer, Cryptography.xor, agree]

/-- One gate's evaluation at a label reads only the slots whose own bit is the evaluated
one: the three hash slots at a `false` bit, the two pad slots at a `true` bit. -/
theorem bitEvaluate_congr (first second : PermutationOracle FixedKeyIndex Block)
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount) (table : BitAdaptor.Table)
    (bit : Bool) (label : Block)
    (agree : ∀ slot : FixedKeySlot, slotBit slot = bit →
      first.permutation ⟨adaptor, position, slot⟩ label =
        second.permutation ⟨adaptor, position, slot⟩ label) :
    BitAdaptor.evaluate (fixedKeyGate first adaptor position.val) table bit label =
      BitAdaptor.evaluate (fixedKeyGate second adaptor position.val) table bit label := by
  unfold BitAdaptor.evaluate
  cases bit with
  | false =>
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    simp only [fixedKeyGate, BitAdaptor.fixedKeyOracle]
    rw [hashBytes_congr first second adaptor position label fun chunk => agree (.hash chunk) rfl]
  | true =>
    rw [if_pos rfl, if_pos rfl]
    simp only [fixedKeyGate, BitAdaptor.fixedKeyOracle]
    rw [padBytes_congr first second adaptor position label fun chunk => agree (.pad chunk) rfl]

/-- One adaptor family's evaluation on the honest labels reads only the slots whose own bit
is the input's bit at that gate. -/
theorem evaluateDigit_congr (first second : PermutationOracle FixedKeyIndex Block)
    (key : InputMacKey) (input : AffineInput) (adaptor : CurveAdaptor) (value : BaseField)
    (bits : inputBits input adaptor = coordinateValues value)
    (tables : Vector BitAdaptor.Table coordinateBitCount)
    (agree : ∀ index : FixedKeyIndex,
      slotBit index.slot = inputBits input index.adaptor index.position →
      first.permutation index (selectedLabel key input index.adaptor index.position) =
        second.permutation index (selectedLabel key input index.adaptor index.position)) :
    CurveMembership.evaluateDigit (fixedKeyGate first adaptor) tables value
        (gateMac (key.encodeAffine input) adaptor) =
      CurveMembership.evaluateDigit (fixedKeyGate second adaptor) tables value
        (gateMac (key.encodeAffine input) adaptor) := by
  unfold CurveMembership.evaluateDigit
  refine congrArg DigitAdaptor.fromBits (funext fun index => ?_)
  simp only [DigitAdaptor.evaluate, Vector.get_ofFn, ← bits, gateMac_encodeAffine]
  exact bitEvaluate_congr first second adaptor index (tables.get index)
    (inputBits input adaptor index) (selectedLabel key input adaptor index)
    fun slot slotIs => agree ⟨adaptor, index, slot⟩ slotIs

/-- The curve evaluation on the honest labels reads the fixed-key oracle only at the
selected label of every gate, and only at the slots that label belongs to. -/
theorem curveEvaluate_congr (first second : PermutationOracle FixedKeyIndex Block)
    (key : InputMacKey) (input : AffineInput) (table : CurveMembership.Table)
    (agree : ∀ index : FixedKeyIndex,
      slotBit index.slot = inputBits input index.adaptor index.position →
      first.permutation index (selectedLabel key input index.adaptor index.position) =
        second.permutation index (selectedLabel key input index.adaptor index.position)) :
    CurveMembership.evaluate (curveOracles first) table input (key.encodeAffine input) =
      CurveMembership.evaluate (curveOracles second) table input (key.encodeAffine input) := by
  have digit : ∀ (adaptor : CurveAdaptor) (value : BaseField),
      inputBits input adaptor = coordinateValues value →
      ∀ tables : Vector BitAdaptor.Table coordinateBitCount,
        CurveMembership.evaluateDigit (fixedKeyGate first adaptor) tables value
            (gateMac (key.encodeAffine input) adaptor) =
          CurveMembership.evaluateDigit (fixedKeyGate second adaptor) tables value
            (gateMac (key.encodeAffine input) adaptor) :=
    fun adaptor value bits tables =>
      evaluateDigit_congr first second key input adaptor value bits tables agree
  have x3 : CurveMembership.evaluateDigit (fixedKeyGate first .x3) table.x3 input.x
      (key.encodeAffine input).x =
      CurveMembership.evaluateDigit (fixedKeyGate second .x3) table.x3 input.x
        (key.encodeAffine input).x := digit .x3 input.x rfl table.x3
  have y4 : CurveMembership.evaluateDigit (fixedKeyGate first .y4) table.y4 input.y
      (key.encodeAffine input).y =
      CurveMembership.evaluateDigit (fixedKeyGate second .y4) table.y4 input.y
        (key.encodeAffine input).y := digit .y4 input.y rfl table.y4
  have x5 : CurveMembership.evaluateDigit (fixedKeyGate first .x5) table.x5 input.x
      (key.encodeAffine input).x =
      CurveMembership.evaluateDigit (fixedKeyGate second .x5) table.x5 input.x
        (key.encodeAffine input).x := digit .x5 input.x rfl table.x5
  have y6 : CurveMembership.evaluateDigit (fixedKeyGate first .y6) table.y6 input.y
      (key.encodeAffine input).y =
      CurveMembership.evaluateDigit (fixedKeyGate second .y6) table.y6 input.y
        (key.encodeAffine input).y := digit .y6 input.y rfl table.y6
  have x7 : CurveMembership.evaluateDigit (fixedKeyGate first .x7) table.x7 input.x
      (key.encodeAffine input).x =
      CurveMembership.evaluateDigit (fixedKeyGate second .x7) table.x7 input.x
        (key.encodeAffine input).x := digit .x7 input.x rfl table.x7
  simp only [CurveMembership.evaluate, curveOracles]
  rw [x3, y4, x5, y6, x7]

/-! ### Programming preserves the agreement of two views -/

/-- Freshness reads the log and the permutation of the request's own index. -/
theorem fresh_congr (firstLog secondLog : List Query)
    (first second : PermutationOracle FixedKeyIndex Block) (request : ProgramRequest)
    (sameLog : firstLog = secondLog)
    (atRequest : first.permutation request.index = second.permutation request.index) :
    request.Fresh firstLog first ↔ request.Fresh secondLog second := by
  unfold ProgramRequest.Fresh
  rw [sameLog, atRequest]

/-- Programming one request preserves the agreement of two views at any index, provided the
two views already agree at the request's own index. -/
theorem programIfFresh_congr_at (first second : State) (request : ProgramRequest)
    (sameLog : first.log = second.log)
    (atRequest : first.view.1.permutation request.index = second.view.1.permutation request.index)
    (index : FixedKeyIndex)
    (here : first.view.1.permutation index = second.view.1.permutation index) :
    (programIfFresh first request).view.1.permutation index =
      (programIfFresh second request).view.1.permutation index := by
  have same := fresh_congr first.log second.log first.view.1 second.view.1 request sameLog
    atRequest
  unfold programIfFresh
  by_cases freshFirst : request.Fresh first.log first.view.1
  · rw [if_pos freshFirst, if_pos (same.mp freshFirst)]
    show (programPermutation first.view.1 request).permutation index =
      (programPermutation second.view.1 request).permutation index
    unfold programPermutation
    by_cases sameIndex : index = request.index
    · simp only [sameIndex, atRequest]
    · simp only [if_neg sameIndex, here]
  · rw [if_neg freshFirst, if_neg fun other => freshFirst (same.mpr other)]
    exact here

/-- Programming a list of requests preserves the agreement of two views at any index,
provided the two views already agree at every request's own index. -/
theorem programAll_congr_at (first second : State) (requests : List ProgramRequest)
    (sameLog : first.log = second.log)
    (agreeAt : ∀ request ∈ requests,
      first.view.1.permutation request.index = second.view.1.permutation request.index)
    (index : FixedKeyIndex)
    (here : first.view.1.permutation index = second.view.1.permutation index) :
    (programAll first requests).view.1.permutation index =
      (programAll second requests).view.1.permutation index := by
  induction requests generalizing first second with
  | nil => exact here
  | cons request rest inductionHypothesis =>
    rw [programAll_cons, programAll_cons]
    exact inductionHypothesis (programIfFresh first request) (programIfFresh second request)
      (by rw [programIfFresh_log, programIfFresh_log, sameLog])
      (fun other member => programIfFresh_congr_at first second request sameLog
        (agreeAt request List.mem_cons_self) other.index
        (agreeAt other (List.mem_cons_of_mem _ member)))
      (programIfFresh_congr_at first second request sameLog
        (agreeAt request List.mem_cons_self) index here)

/-- Programming leaves every index no request names alone. -/
theorem programAll_untouched (state : State) (requests : List ProgramRequest)
    (index : FixedKeyIndex) (untouched : ∀ request ∈ requests, request.index ≠ index) :
    (programAll state requests).view.1.permutation index = state.view.1.permutation index := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest inductionHypothesis =>
    rw [programAll_cons, inductionHypothesis (programIfFresh state request)
      fun other member => untouched other (List.mem_cons_of_mem _ member)]
    unfold programIfFresh
    split
    · show (programPermutation state.view.1 request).permutation index = _
      unfold programPermutation
      exact if_neg fun equal => untouched request List.mem_cons_self equal.symm
    · rfl

/-- Two views that answer a query identically still answer it identically after the same
requests are programmed, provided they agree at every request's own index. -/
theorem publicAnswer_programAll_congr (first second : State) (requests : List ProgramRequest)
    (sameLog : first.log = second.log) (sameRest : first.view.2 = second.view.2)
    (agreeAt : ∀ request ∈ requests,
      first.view.1.permutation request.index = second.view.1.permutation request.index)
    (query : Query)
    (agreeQuery : publicAnswer first.view query = publicAnswer second.view query) :
    publicAnswer (programAll first requests).view query =
      publicAnswer (programAll second requests).view query := by
  have atIndex (index : FixedKeyIndex) :
      (programAll first requests).view.1.permutation index =
          (programAll second requests).view.1.permutation index ∨
        ((programAll first requests).view.1.permutation index =
            first.view.1.permutation index ∧
          (programAll second requests).view.1.permutation index =
            second.view.1.permutation index) := by
    by_cases touched : ∃ request ∈ requests, request.index = index
    · obtain ⟨request, member, rfl⟩ := touched
      exact Or.inl (programAll_congr_at first second requests sameLog agreeAt request.index
        (agreeAt request member))
    · have untouched : ∀ request ∈ requests, request.index ≠ index := by
        intro request member equal
        exact touched ⟨request, member, equal⟩
      exact Or.inr ⟨programAll_untouched first requests index untouched,
        programAll_untouched second requests index untouched⟩
  refine publicAnswer_view_congr _ _ query
    (by rw [programAll_view_snd, programAll_view_snd]; exact sameRest) ?_ ?_
  · rintro index value rfl
    rcases atIndex index with same | ⟨left, right⟩
    · rw [same]
    · rw [left, right]
      exact agreeQuery
  · rintro index value rfl
    rcases atIndex index with same | ⟨left, right⟩
    · rw [same]
    · rw [left, right]
      exact agreeQuery

noncomputable section

/-! ### The simulated second stage as a programming -/

/-- The program requests the simulated second stage issues: none when the input needs no
steering, the steering requests otherwise. -/
def simulateRequestLaw [FieldCertificate] [GroupCertificate] (state : State)
    (input : AffineInput) (output : Option Point) : PMF (List ProgramRequest) :=
  (steeringTarget state.carrier input output).elim (PMF.pure [])
    fun target => steerRequestLaw state.view state.table input
      (state.inputMacKey.encodeAffine input) target

theorem simulateRequestLaw_none [FieldCertificate] [GroupCertificate] (state : State)
    (input : AffineInput) (output : Option Point)
    (noTarget : steeringTarget state.carrier input output = none) :
    simulateRequestLaw state input output = PMF.pure [] := by
  unfold simulateRequestLaw
  rw [noTarget]
  rfl

theorem simulateRequestLaw_some [FieldCertificate] [GroupCertificate] (state : State)
    (input : AffineInput) (output : Option Point) (target : BaseField)
    (hasTarget : steeringTarget state.carrier input output = some target) :
    simulateRequestLaw state input output =
      steerRequestLaw state.view state.table input (state.inputMacKey.encodeAffine input)
        target := by
  unfold simulateRequestLaw
  rw [hasTarget]
  rfl

/-- The simulated encoding is its request law followed by the programming. -/
theorem simulateEncode_eq_map [FieldCertificate] [GroupCertificate] (state : State)
    (input : AffineInput) (output : Option Point) :
    simulateEncode state input output =
      (simulateRequestLaw state input output).map fun requests =>
        (Lamport.selectedLabels (state.inputMacKey.encodeAffine input),
          programAll state requests) := by
  cases targetCase : steeringTarget state.carrier input output with
  | none =>
    rw [simulateRequestLaw_none state input output targetCase, PMF.pure_map]
    simp only [simulateEncode, targetCase]
    rfl
  | some target =>
    rw [simulateRequestLaw_some state input output target targetCase]
    simp only [simulateEncode, targetCase]
    rw [steer_eq_map, PMF.map_comp]
    rfl

/-- The simulated second stage is its request law, the programming, and the decision run. -/
theorem simulatedStageTwo_eq [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (circuit : Garbling.Public) (input : AffineInput)
    (output : Option Point) (advState : adversary.State) (state : State) :
    simulatedStageTwo adversary parameter auxiliary circuit input output advState state =
      (simulateRequestLaw state input output).bind fun requests =>
        ((adversary.decide parameter circuit
            (Lamport.selectedLabels (state.inputMacKey.encodeAffine input)) auxiliary
            advState).run idealOracle (programAll state requests)).map loggedOutcome := by
  unfold simulatedStageTwo
  rw [simulateEncode_eq_map, PMF.bind_map]
  rfl

/-- Every steering request sits at the steering gate, on a slot whose own bit is the bit
the input selects there. -/
theorem steerRequestLaw_support (view : View) (table : CurveMembership.Table)
    (input : AffineInput) (mac : InputMac) (target : BaseField) (requests : List ProgramRequest)
    (member : requests ∈ (steerRequestLaw view table input mac target).support)
    (request : ProgramRequest) (inList : request ∈ requests) :
    slotBit request.index.slot =
      inputBits input request.index.adaptor request.index.position := by
  unfold steerRequestLaw at member
  simp only at member
  split at member
  · rename_i set
    rw [PMF.mem_support_pure_iff] at member
    subst member
    simp only [padRequests, List.mem_cons, List.not_mem_nil, or_false] at inList
    rcases inList with rfl | rfl <;>
      · show true = inputBits input .x7 0
        rw [← steeringBit_eq]
        exact set.symm
  · rename_i unset
    rw [PMF.support_map] at member
    obtain ⟨hash, _, rfl⟩ := member
    simp only [hashRequests, List.mem_cons, List.not_mem_nil, or_false] at inList
    rcases inList with rfl | rfl | rfl <;>
      · show false = inputBits input .x7 0
        rw [← steeringBit_eq]
        exact (Bool.not_eq_true _ ▸ unset).symm

/-- Every request the simulated second stage issues sits on a slot that reads the label the
input selects. -/
theorem simulateRequestLaw_support [FieldCertificate] [GroupCertificate] (state : State)
    (input : AffineInput) (output : Option Point) (requests : List ProgramRequest)
    (member : requests ∈ (simulateRequestLaw state input output).support)
    (request : ProgramRequest) (inList : request ∈ requests) :
    slotBit request.index.slot =
      inputBits input request.index.adaptor request.index.position := by
  cases targetCase : steeringTarget state.carrier input output with
  | none =>
    rw [simulateRequestLaw_none state input output targetCase,
      PMF.mem_support_pure_iff] at member
    subst member
    simp only [List.not_mem_nil] at inList
  | some target =>
    rw [simulateRequestLaw_some state input output target targetCase] at member
    exact steerRequestLaw_support _ _ _ _ _ requests member request inList

/-- The steering request law reads the fixed-key oracle only at the selected labels. -/
theorem steerRequestLaw_congr (firstView secondView : View) (table : CurveMembership.Table)
    (key : InputMacKey) (input : AffineInput) (target : BaseField)
    (agree : ∀ index : FixedKeyIndex,
      slotBit index.slot = inputBits input index.adaptor index.position →
      firstView.1.permutation index (selectedLabel key input index.adaptor index.position) =
        secondView.1.permutation index (selectedLabel key input index.adaptor index.position)) :
    steerRequestLaw firstView table input (key.encodeAffine input) target =
      steerRequestLaw secondView table input (key.encodeAffine input) target := by
  have released := curveEvaluate_congr firstView.1 secondView.1 key input table agree
  have gate : BitAdaptor.evaluate (fixedKeyGate firstView.1 .x7 0) (table.x7.get 0)
      (steeringBit input) ((key.encodeAffine input).x.get 0) =
      BitAdaptor.evaluate (fixedKeyGate secondView.1 .x7 0) (table.x7.get 0)
        (steeringBit input) ((key.encodeAffine input).x.get 0) := by
    rw [steeringBit_eq, show ((key.encodeAffine input).x.get 0) = selectedLabel key input .x7 0
      from gateMac_encodeAffine key input .x7 0]
    exact bitEvaluate_congr firstView.1 secondView.1 .x7 0 (table.x7.get 0)
      (inputBits input .x7 0) (selectedLabel key input .x7 0)
      fun slot slotIs => agree ⟨.x7, 0, slot⟩ slotIs
  unfold steerRequestLaw
  simp only
  rw [released, gate]

/-- The simulated second stage cannot tell two views apart when they agree as permutations
at every index whose slot reads a selected label and answer every good query identically:
the steering issues the same request list on both, and that list names only indices where
the two views agree outright. -/
theorem simulatedStageTwo_agree [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (circuit : Garbling.Public) (input : AffineInput)
    (output : Option Point) (advState : adversary.State)
    (first second : PermutationOracle FixedKeyIndex Block)
    (rest : PermutationOracle Garbling.EncIndex Block × (BaseField → Block × Block))
    (priorLog : List Query) (carrier : NonZeroBase) (key : InputMacKey) (bad : Query → Prop)
    (selectedAt : ∀ index : FixedKeyIndex,
      slotBit index.slot = inputBits input index.adaptor index.position →
      first.permutation index = second.permutation index)
    (agreeOff : ∀ query, ¬ bad query →
      publicAnswer ((first, rest) : View) query = publicAnswer ((second, rest) : View) query)
    (result : Bool) (log : List Query) (good : ∀ query ∈ log, ¬ bad query) :
    simulatedStageTwo adversary parameter auxiliary circuit input output advState
        (stageTwoState (first, rest) priorLog circuit.1 carrier key) (result, log) =
      simulatedStageTwo adversary parameter auxiliary circuit input output advState
        (stageTwoState (second, rest) priorLog circuit.1 carrier key) (result, log) := by
  have atLabel : ∀ index : FixedKeyIndex,
      slotBit index.slot = inputBits input index.adaptor index.position →
      first.permutation index (selectedLabel key input index.adaptor index.position) =
        second.permutation index (selectedLabel key input index.adaptor index.position) :=
    fun index selected => congrArg
      (fun equiv : Block ≃ Block => equiv (selectedLabel key input index.adaptor index.position))
      (selectedAt index selected)
  have sameLaw : simulateRequestLaw (stageTwoState (first, rest) priorLog circuit.1 carrier key)
        input output =
      simulateRequestLaw (stageTwoState (second, rest) priorLog circuit.1 carrier key) input
        output := by
    have carrierIs : ∀ oracle : PermutationOracle FixedKeyIndex Block,
        (stageTwoState (oracle, rest) priorLog circuit.1 carrier key).carrier = carrier :=
      fun _ => rfl
    cases targetCase : steeringTarget carrier input output with
    | none =>
      rw [simulateRequestLaw_none _ _ _ (by rw [carrierIs]; exact targetCase),
        simulateRequestLaw_none _ _ _ (by rw [carrierIs]; exact targetCase)]
    | some target =>
      rw [simulateRequestLaw_some _ _ _ target (by rw [carrierIs]; exact targetCase),
        simulateRequestLaw_some _ _ _ target (by rw [carrierIs]; exact targetCase)]
      simp only [stageTwoState_view, stageTwoState_table, stageTwoState_inputMacKey]
      exact steerRequestLaw_congr (first, rest) (second, rest) circuit.1 key input target atLabel
  rw [simulatedStageTwo_eq, simulatedStageTwo_eq]
  simp only [stageTwoState_inputMacKey]
  rw [sameLaw, PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun requests => ?_
  by_cases member : requests ∈
    (simulateRequestLaw (stageTwoState (second, rest) priorLog circuit.1 carrier key) input
      output).support
  · have runAgree := run_idealOracle_agree
      (adversary.decide parameter circuit
        (Lamport.selectedLabels (key.encodeAffine input)) auxiliary advState) bad
      (programAll (stageTwoState (first, rest) priorLog circuit.1 carrier key) requests)
      (programAll (stageTwoState (second, rest) priorLog circuit.1 carrier key) requests)
      (by rw [programAll_log, programAll_log, stageTwoState_log, stageTwoState_log])
      ?_ result log good
    · rw [runAgree]
    · intro query notBad
      refine publicAnswer_programAll_congr
        (stageTwoState (first, rest) priorLog circuit.1 carrier key)
        (stageTwoState (second, rest) priorLog circuit.1 carrier key) requests rfl rfl ?_ query
        (agreeOff query notBad)
      intro request inList
      exact selectedAt request.index (simulateRequestLaw_support _ input output requests member
        request inList)
  · rw [(PMF.apply_eq_zero_iff _ _).mpr member, zero_mul, zero_mul]

/-! ### The two simulated second stages of the second oracle hop -/

/-- The simulated second stage on the view programmed at every used label. -/
def usedSimulatedStageTwo [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (circuit : Garbling.Public) (input : AffineInput)
    (output : Option Point) (advState : adversary.State) (key : InputMacKey)
    (values : FixedKeyIndex → Block) (view : View) (priorLog : List Query)
    (carrier : NonZeroBase) : PMF (Bool × List Query) :=
  simulatedStageTwo adversary parameter auxiliary circuit input output advState
    (stageTwoState (programIndices (usedPrograms key values) view.1, view.2) priorLog circuit.1
      carrier key)

/-- The simulated second stage on the view programmed at the selected labels only. -/
def selectedSimulatedStageTwo [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (circuit : Garbling.Public) (input : AffineInput)
    (output : Option Point) (advState : adversary.State) (outputs : GateValues BaseField)
    (fibers : GateValues (BitVec 384)) (state : State) : PMF (Bool × List Query) :=
  simulatedStageTwo adversary parameter auxiliary circuit input output advState
    (programSelected state input outputs fibers)

/-- Programming the selected labels of a second-stage state is again a second-stage state. -/
theorem programSelected_stageTwoState (view : View) (priorLog : List Query)
    (table : CurveMembership.Table) (carrier : NonZeroBase) (key : InputMacKey)
    (input : AffineInput) (outputs : GateValues BaseField) (fibers : GateValues (BitVec 384)) :
    programSelected (stageTwoState view priorLog table carrier key) input outputs fibers =
      stageTwoState (programIndices (selectedPrograms key input outputs (tableRow table) fibers)
        view.1, view.2) priorLog table carrier key := rfl

/-- The simulated second stage on the selected programming never reads the labels the input
leaves unselected. -/
theorem selectedSimulatedStageTwo_unread [FieldCertificate] [GroupCertificate]
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) (circuit : Garbling.Public)
    (input : AffineInput) (output : Option Point) (advState : adversary.State)
    (outputs : GateValues BaseField) (fibers : GateValues (BitVec 384)) (view : View)
    (priorLog : List Query) (table : CurveMembership.Table) (carrier : NonZeroBase)
    (key : InputMacKey) (blocks : LabelIndex → Block) :
    selectedSimulatedStageTwo adversary parameter auxiliary circuit input output advState outputs
        fibers (stageTwoState view priorLog table carrier
          (setKeyLabels key (unreadLabelBits input) blocks)) =
      selectedSimulatedStageTwo adversary parameter auxiliary circuit input output advState
        outputs fibers (stageTwoState view priorLog table carrier key) := by
  unfold selectedSimulatedStageTwo
  rw [programSelected_stageTwoState, programSelected_stageTwoState, selectedPrograms_setKeyLabels]
  exact simulatedStageTwo_unread adversary parameter auxiliary circuit input output advState
    (programIndices (selectedPrograms key input outputs (tableRow table) fibers) view.1, view.2)
    priorLog table carrier key blocks

/-- The log of the simulated second stage is the first stage's log plus the second budget. -/
theorem simulatedStageTwo_length [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (circuit : Garbling.Public) (input : AffineInput)
    (output : Option Point) (advState : adversary.State) (state : State)
    (outcome : Bool × List Query)
    (member : outcome ∈ (simulatedStageTwo adversary parameter auxiliary circuit input output
      advState state).support) :
    outcome.2.length ≤ state.log.length + adversary.secondQueryBudget parameter := by
  rw [simulatedStageTwo_eq, PMF.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨requests, _, member⟩ := member
  rw [PMF.support_map] at member
  obtain ⟨result, resultMember, rfl⟩ := member
  have bound := run_idealOracle_log_length _ _ result resultMember
  rw [programAll_log] at bound
  exact bound

/-- At an index whose slot reads the selected label, the two views of the second oracle hop
are the same permutation, so the steering cannot tell them apart. -/
theorem programIndices_selected_congr (oracle : PermutationOracle FixedKeyIndex Block)
    (key : InputMacKey) (input : AffineInput) (bridgeKey mask r1 r2 : BaseField)
    (digests : GateValues (BitVec 384)) (pads : GateValues BitAdaptor.Ciphertext)
    (index : FixedKeyIndex)
    (selected : slotBit index.slot = inputBits input index.adaptor index.position) :
    (programIndices (usedPrograms key (freshValue digests pads)) oracle).permutation index =
      (programIndices (selectedPrograms key input
        (encodeCoordinates input (digestedRaw mask r1 r2 digests pads)).hash
        (tableRow (Coordinates.table bridgeKey key (digestedRaw mask r1 r2 digests pads)))
        digests) oracle).permutation index :=
  programIndices_congr_at _ _ oracle index
    (selectedPrograms_selected key input bridgeKey mask r1 r2 digests pads index selected).symm

/-- Off the bad label values of the whole log, the simulated second stage cannot tell the
first hop's programming at every used label from the reference game's programming at the
selected labels only. -/
theorem usedSimulatedStageTwo_agree [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (circuit : Garbling.Public) (input : AffineInput)
    (output : Option Point) (advState : adversary.State)
    (oracle : PermutationOracle FixedKeyIndex Block)
    (rest : PermutationOracle Garbling.EncIndex Block × (BaseField → Block × Block))
    (priorLog : List Query) (carrier : NonZeroBase) (key : InputMacKey)
    (bridgeKey mask r1 r2 : BaseField) (digests : GateValues (BitVec 384))
    (pads : GateValues BitAdaptor.Ciphertext)
    (tableSame : circuit.1 =
      Coordinates.table bridgeKey key (digestedRaw mask r1 r2 digests pads))
    (result : Bool) (log : List Query)
    (good : ∀ query ∈ log,
      ¬ SelectedBad oracle (freshValue digests pads) key input query) :
    usedSimulatedStageTwo adversary parameter auxiliary circuit input output advState key
        (freshValue digests pads) (oracle, rest) priorLog carrier (result, log) =
      selectedSimulatedStageTwo adversary parameter auxiliary circuit input output advState
        (encodeCoordinates input (digestedRaw mask r1 r2 digests pads)).hash digests
        (stageTwoState (oracle, rest) priorLog circuit.1 carrier key) (result, log) := by
  unfold usedSimulatedStageTwo selectedSimulatedStageTwo
  rw [programSelected_stageTwoState,
    show tableRow circuit.1 =
      tableRow (Coordinates.table bridgeKey key (digestedRaw mask r1 r2 digests pads)) from
    congrArg tableRow tableSame]
  exact simulatedStageTwo_agree adversary parameter auxiliary circuit input output advState _ _
    rest priorLog carrier key (SelectedBad oracle (freshValue digests pads) key input)
    (fun index selected => programIndices_selected_congr oracle key input bridgeKey mask r1 r2
      digests pads index selected)
    (fun query notBad => publicAnswer_selectedPrograms oracle rest key input bridgeKey mask r1 r2
      digests pads query notBad)
    result log good

/-! ### The simulated game in two-stage shape -/

/-- A simulated-shaped game: the first stage runs on `firstView`, the second stage on
`secondView` with the simulator's labels and steering. -/
def simulatedTwoStage [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (scalar : NonZeroScalar) (circuit : Garbling.Public)
    (carrier : NonZeroBase) (key : InputMacKey) (firstView secondView : View) : PMF Bool :=
  (loggedFirstStage adversary parameter auxiliary circuit firstView).bind fun outcome =>
    (simulatedStageTwo adversary parameter auxiliary circuit outcome.1.1
      (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2
      (stageTwoState secondView outcome.2 circuit.1 carrier key)).map Prod.fst

/-- One round of the simulated game on explicit coordinates: the table is garbled on the
view's own fixed-key oracle and both stages run on that view. -/
def simulatedOn [FieldCertificate] [GroupCertificate] (adversary : Adversary) (parameter : Nat)
    (auxiliary : Unit) (scalar : NonZeroScalar) (bridgeKey mask r1 r2 : BaseField)
    (carrier : NonZeroBase) (key : InputMacKey) (view : View) : PMF Bool :=
  simulatedTwoStage adversary parameter auxiliary scalar
    (CurveMembership.garble bridgeKey mask r1 r2 (curveOracles view.1) key, carrierBits carrier)
    carrier key view view

/-- The simulated game is one round of `simulatedOn` on a uniform tape and carrier. -/
theorem simulatedGame_eq_simulatedOn [FieldCertificate] [GroupCertificate]
    (adversary : Adversary) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) simulator idealOracle adversary
        parameter scalar auxiliary =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
          simulatedOn adversary parameter auxiliary scalar tape.bridgeKey.value
            tape.curveMask.value tape.curveR1 tape.curveR2 carrier tape.inputMacKey
            (Garbling.evaluationOracle tape) := by
  rw [simulatedGame_eq]
  refine congrArg (PMF.bind _) (funext fun tape => ?_)
  refine congrArg (PMF.bind _) (funext fun carrier => ?_)
  have conditioned : (((adversary.chooseInput parameter (curveTable tape, carrierBits carrier)
        auxiliary).run idealOracle (initialState tape (curveTable tape) carrier)).bind
      fun selected => (simulatedStageTwo adversary parameter auxiliary
        (curveTable tape, carrierBits carrier) selected.1.1
        (checkedScalarMultiplication scalar.value selected.1.1) selected.1.2
        selected.2).map Prod.fst) =
      (((adversary.chooseInput parameter (curveTable tape, carrierBits carrier)
        auxiliary).run idealOracle (initialState tape (curveTable tape) carrier)).bind
      fun selected => (simulatedStageTwo adversary parameter auxiliary
        (curveTable tape, carrierBits carrier) selected.1.1
        (checkedScalarMultiplication scalar.value selected.1.1) selected.1.2
        (stageTwoState (Garbling.evaluationOracle tape) selected.2.log (curveTable tape)
          carrier tape.inputMacKey)).map Prod.fst) := by
    refine bind_congr_support fun selected member => ?_
    obtain ⟨sameView, sameTable, sameCarrier, sameKey⟩ :=
      run_idealOracle_support _ _ selected member
    rw [← eq_stageTwoState (Garbling.evaluationOracle tape) (curveTable tape) carrier
      tape.inputMacKey selected.2 sameView sameTable sameCarrier sameKey]
  have circuitEq : (CurveMembership.garble tape.bridgeKey.value tape.curveMask.value
      tape.curveR1 tape.curveR2 (curveOracles (Garbling.evaluationOracle tape).1)
      tape.inputMacKey, carrierBits carrier) = (curveTable tape, carrierBits carrier) := rfl
  rw [conditioned]
  unfold simulatedOn simulatedTwoStage
  rw [circuitEq, ← map_loggedOutcome_firstState adversary parameter auxiliary
    (curveTable tape, carrierBits carrier) (Garbling.evaluationOracle tape) (curveTable tape)
    carrier tape.inputMacKey, PMF.bind_map]
  rfl

/-- The simulated game with the bridge key, the label key, the fixed-key oracle and the
curve coordinates sampled separately from the rest of the tape. -/
theorem simulatedGame_eq_split [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) simulator idealOracle adversary
        parameter scalar auxiliary =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype InputMacKey).bind fun key =>
          (PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
            (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
              (PMF.uniformOfFintype (NonZeroBase × BaseField × BaseField)).bind fun curve =>
                (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
                  simulatedOn adversary parameter auxiliary scalar bridgeKey.value
                    curve.1.value curve.2.1 curve.2.2 carrier key
                    (oracle, tape.encOracle, tape.hashOracle) := by
  rw [simulatedGame_eq_simulatedOn, ← uniform_bind_setCurve, ← uniform_bind_setOracle,
    ← uniform_bind_setBridge, ← uniform_bind_setKey]
  rfl

/-- The S side after the first hop: the oracle is programmed at every used label to the
fresh value of that slot, and the released table is the reference table of the fresh
per-gate digests and pads. -/
def simulatedFresh [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (scalar : NonZeroScalar) (bridgeKey : BaseField)
    (carrier : NonZeroBase) (key : InputMacKey)
    (rest : PermutationOracle Garbling.EncIndex Block × (BaseField → Block × Block))
    (oracle : PermutationOracle FixedKeyIndex Block) (mask r1 r2 : BaseField)
    (secrets : GateValues (BitVec 384) × GateValues BitAdaptor.Ciphertext) : PMF Bool :=
  simulatedTwoStage adversary parameter auxiliary scalar
    (Coordinates.table bridgeKey key ⟨mask, r1, r2, digestField secrets.1, secrets.2⟩,
      carrierBits carrier) carrier key
    (programIndices (usedPrograms key (freshValue secrets.1 secrets.2)) oracle, rest)
    (programIndices (usedPrograms key (freshValue secrets.1 secrets.2)) oracle, rest)

/-- Step 4 of the chain, exact: the simulated game is the reparametrised game. -/
theorem simulatedGame_eq_fresh [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) simulator idealOracle adversary
        parameter scalar auxiliary =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype InputMacKey).bind fun key =>
          (PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
            (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
              (PMF.uniformOfFintype (GateValues (BitVec 384) ×
                  GateValues BitAdaptor.Ciphertext)).bind fun secrets =>
                (PMF.uniformOfFintype (NonZeroBase × BaseField × BaseField)).bind fun curve =>
                  (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
                    simulatedFresh adversary parameter auxiliary scalar bridgeKey.value carrier
                      key (tape.encOracle, tape.hashOracle) oracle curve.1.value curve.2.1
                      curve.2.2 secrets := by
  rw [simulatedGame_eq_split]
  refine congrArg (PMF.bind _) (funext fun tape => ?_)
  refine congrArg (PMF.bind _) (funext fun key => ?_)
  refine congrArg (PMF.bind _) (funext fun bridgeKey => ?_)
  rw [← uniform_bind_usedPrograms key]
  refine congrArg (PMF.bind _) (funext fun oracle => ?_)
  refine congrArg (PMF.bind _) (funext fun secrets => ?_)
  refine congrArg (PMF.bind _) (funext fun curve => ?_)
  refine congrArg (PMF.bind _) (funext fun carrier => ?_)
  unfold simulatedOn simulatedFresh
  rw [show (curveOracles ((programFamily (usedLabel key)
        (oracle, freshOfSecrets key secrets.1 secrets.2)).1, tape.encOracle, tape.hashOracle).1) =
      curveOracles (programFamily (usedLabel key)
        (oracle, freshOfSecrets key secrets.1 secrets.2)).1 from rfl,
    curveGarble_programFamily, freshHash_freshOfSecrets, freshPad_freshOfSecrets,
    programFamily_eq_programIndices]

/-! ### The S side of the chain, assembled -/

/-- The key-free sample of the S side: the tape's own bridge key `u`, and the same key-free
sample as the hybrid side -- the tape's unread oracles, the unprogrammed fixed-key oracle,
the fresh per-gate digests and pads, the curve coordinates and the carrier. -/
abbrev SimulatedDatum := NonZeroBase × HybridDatum

/-- The law of the key-free sample of the S side. -/
def simulatedData : PMF SimulatedDatum :=
  (PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
    (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
      (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype (GateValues (BitVec 384) ×
            GateValues BitAdaptor.Ciphertext)).bind fun secrets =>
          (PMF.uniformOfFintype (NonZeroBase × BaseField × BaseField)).bind fun curve =>
            (PMF.uniformOfFintype NonZeroBase).map fun carrier =>
              (bridgeKey, tape, oracle, secrets, curve, carrier)

theorem simulatedData_bind {Outcome : Type} (continuation : SimulatedDatum → PMF Outcome) :
    simulatedData.bind continuation =
      (PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
          (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
            (PMF.uniformOfFintype (GateValues (BitVec 384) ×
                GateValues BitAdaptor.Ciphertext)).bind fun secrets =>
              (PMF.uniformOfFintype (NonZeroBase × BaseField × BaseField)).bind fun curve =>
                (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
                  continuation (bridgeKey, tape, oracle, secrets, curve, carrier) := by
  unfold simulatedData
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

/-- The bridge key of one sample: the tape's own `u`, independent of the carrier. -/
def simulatedBridgeKey (datum : SimulatedDatum) : BaseField := datum.1.value

/-- The public value of one sample. It does not depend on the label key. -/
def simulatedCircuit (datum : SimulatedDatum) : Garbling.Public :=
  (Coordinates.table (simulatedBridgeKey datum) witnessTape.inputMacKey (hybridRaw datum.2),
    carrierBits (hybridCarrier datum.2))

theorem simulatedCircuit_table (key : InputMacKey) (datum : SimulatedDatum) :
    (simulatedCircuit datum).1 =
      Coordinates.table (simulatedBridgeKey datum) key
        (digestedRaw (hybridMask datum.2) (hybridR1 datum.2) (hybridR2 datum.2)
          (hybridDigests datum.2) (hybridPads datum.2)) :=
  Coordinates.table_key _ _ _ _

/-- The S side after the first hop, in the shape the two oracle hops consume. -/
theorem simulatedGame_eq_used [FieldCertificate] [GroupCertificate] (adversary : Adversary)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) simulator idealOracle adversary
        parameter scalar auxiliary =
      (PMF.uniformOfFintype InputMacKey).bind fun key => simulatedData.bind fun datum =>
        (loggedFirstStage adversary parameter auxiliary (simulatedCircuit datum)
            (programIndices (usedPrograms key (freshValue (hybridDigests datum.2)
                (hybridPads datum.2))) (hybridView datum.2).1,
              (hybridView datum.2).2)).bind fun outcome =>
          (usedSimulatedStageTwo adversary parameter auxiliary (simulatedCircuit datum)
            outcome.1.1 (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2 key
            (freshValue (hybridDigests datum.2) (hybridPads datum.2)) (hybridView datum.2)
            outcome.2 (hybridCarrier datum.2)).map Prod.fst := by
  rw [simulatedGame_eq_fresh,
    PMF.bind_comm (PMF.uniformOfFintype Garbling.Randomness) (PMF.uniformOfFintype InputMacKey)]
  refine congrArg (PMF.bind _) (funext fun key => ?_)
  rw [PMF.bind_comm (PMF.uniformOfFintype Garbling.Randomness)
    (PMF.uniformOfFintype NonZeroBase), simulatedData_bind]
  refine congrArg (PMF.bind _) (funext fun bridgeKey => ?_)
  refine congrArg (PMF.bind _) (funext fun tape => ?_)
  refine congrArg (PMF.bind _) (funext fun oracle => ?_)
  refine congrArg (PMF.bind _) (funext fun secrets => ?_)
  refine congrArg (PMF.bind _) (funext fun curve => ?_)
  refine congrArg (PMF.bind _) (funext fun carrier => ?_)
  unfold simulatedFresh simulatedTwoStage
  rw [show (Coordinates.table bridgeKey.value key
        ⟨curve.1.value, curve.2.1, curve.2.2, digestField secrets.1, secrets.2⟩,
        carrierBits carrier) =
      simulatedCircuit (bridgeKey, tape, oracle, secrets, curve, carrier) from
    congrArg (fun table => (table, carrierBits carrier))
      (Coordinates.table_key _ _ _ _)]
  rfl

/-- The S side after both oracle hops: the first stage runs on the unprogrammed view and
the second stage -- the simulator's labels and steering -- on the view programmed at the
selected labels only, with the fresh digests in place of the reference game's fiber
sample. -/
def steeredDigested [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) : PMF Bool :=
  (PMF.uniformOfFintype InputMacKey).bind fun key => simulatedData.bind fun datum =>
    (loggedFirstStage adversary parameter auxiliary (simulatedCircuit datum)
        (hybridView datum.2)).bind fun outcome =>
      (selectedSimulatedStageTwo adversary parameter auxiliary (simulatedCircuit datum)
        outcome.1.1 (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2
        (encodeCoordinates outcome.1.1 (hybridRaw datum.2)).hash (hybridDigests datum.2)
        (stageTwoState (hybridView datum.2) outcome.2 (simulatedCircuit datum).1
          (hybridCarrier datum.2) key)).map Prod.fst

/-- Steps 4, 5 and 6 of the chain: the simulated game is within `4 (q₁ + q₂) / 2 ^ 128` of
the reference-shaped game of the tape's own bridge key, with the steering still in place,
the fresh digests still in place of the reference game's fiber sample and the nonzero mask
still in place of the uniform one. -/
theorem advantage_simulatedGame_steeredDigested_le [FieldCertificate] [GroupCertificate]
    (adversary : Adversary) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    advantage
        (idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) simulator idealOracle
          adversary parameter scalar auxiliary)
        (steeredDigested scalar adversary parameter auxiliary) ≤
      4 * ((adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 := by
  have firstHop := advantage_firstView_le adversary parameter auxiliary simulatedData
    (fun datum => hybridView datum.2) simulatedCircuit (fun datum => hybridCarrier datum.2)
    (fun datum => freshValue (hybridDigests datum.2) (hybridPads datum.2))
    fun key datum outcome => (usedSimulatedStageTwo adversary parameter auxiliary
      (simulatedCircuit datum) outcome.1.1
      (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2 key
      (freshValue (hybridDigests datum.2) (hybridPads datum.2)) (hybridView datum.2) outcome.2
      (hybridCarrier datum.2)).map Prod.fst
  have secondHop := advantage_secondStage_le adversary parameter auxiliary simulatedData
    (fun datum => hybridView datum.2) simulatedCircuit
    (fun datum => freshValue (hybridDigests datum.2) (hybridPads datum.2))
    (fun key datum outcome => usedSimulatedStageTwo adversary parameter auxiliary
      (simulatedCircuit datum) outcome.1.1
      (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2 key
      (freshValue (hybridDigests datum.2) (hybridPads datum.2)) (hybridView datum.2) outcome.2
      (hybridCarrier datum.2))
    (fun key datum outcome => selectedSimulatedStageTwo adversary parameter auxiliary
      (simulatedCircuit datum) outcome.1.1
      (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2
      (encodeCoordinates outcome.1.1 (hybridRaw datum.2)).hash (hybridDigests datum.2)
      (stageTwoState (hybridView datum.2) outcome.2 (simulatedCircuit datum).1
        (hybridCarrier datum.2) key))
    (fun key datum outcome result log good =>
      usedSimulatedStageTwo_agree adversary parameter auxiliary (simulatedCircuit datum)
        outcome.1.1 (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2
        (hybridView datum.2).1 (hybridView datum.2).2 outcome.2 (hybridCarrier datum.2) key
        (simulatedBridgeKey datum) (hybridMask datum.2) (hybridR1 datum.2) (hybridR2 datum.2)
        (hybridDigests datum.2) (hybridPads datum.2) (simulatedCircuit_table key datum)
        result log good)
    (fun key datum outcome blocks =>
      selectedSimulatedStageTwo_unread adversary parameter auxiliary (simulatedCircuit datum)
        outcome.1.1 (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2 _
        (hybridDigests datum.2) (hybridView datum.2) outcome.2 (simulatedCircuit datum).1
        (hybridCarrier datum.2) key blocks)
    (fun key datum outcome result member => by
      have bound := simulatedStageTwo_length adversary parameter auxiliary
        (simulatedCircuit datum) outcome.1.1
        (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2
        (programSelected (stageTwoState (hybridView datum.2) outcome.2
          (simulatedCircuit datum).1 (hybridCarrier datum.2) key) outcome.1.1
          (encodeCoordinates outcome.1.1 (hybridRaw datum.2)).hash (hybridDigests datum.2))
        result member
      rw [programSelected_log, stageTwoState_log] at bound
      exact bound)
  rw [← simulatedGame_eq_used] at firstHop
  refine le_trans (advantage_trans _ _ _ _ _ firstHop secondHop) ?_
  have budgets : (adversary.firstQueryBudget parameter : ℝ) ≤
      ((adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter : Nat) : ℝ) := by
    rw [Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have step : 2 * (adversary.firstQueryBudget parameter : ℝ) / 2 ^ 128 ≤
      2 * ((adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 := by
    gcongr
  calc 2 * (adversary.firstQueryBudget parameter : ℝ) / 2 ^ 128 +
        2 * ((adversary.firstQueryBudget parameter +
          adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128
      ≤ 2 * ((adversary.firstQueryBudget parameter +
            adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 +
          2 * ((adversary.firstQueryBudget parameter +
            adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 :=
        add_le_add step le_rfl
    _ = 4 * ((adversary.firstQueryBudget parameter +
          adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 := by ring

end

end Kriterion.ArgoMAC.Security
