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
      (by rw [programAll_log, programAll_log, stageTwoState_log, stageTwoState_log]) ?_ result log good
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
