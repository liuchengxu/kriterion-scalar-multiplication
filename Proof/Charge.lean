/-
This file is the deterministic skeleton of the *charge* half of the steering
hop: the first of the two steps of step 7, and the one that must run first.

The steered reference game's second stage does four things -- it samples the
honest fibers, programs the selected labels, samples a second fiber for the
steering gate, and programs that gate again. The shifted reference game of
`Proof/Shifted.lean` does two -- it samples one fiber family at the shifted
outputs and programs once. This file rewrites the first into the shape of the
second, leaving exactly the gap the probabilistic charge has to pay:

* `selectedSimulatedStageTwo_double` -- on the curve, and when the steering's
  own requests are fresh against the first stage's log, the steered second
  stage is *one* extra fiber sample followed by the hybrid second stage on the
  **doubly programmed** view: the unprogrammed family programmed at the
  selected labels and then again at the steering gate.
* `steeringIndices`, `selectedPrograms_setSteering`, `steeredPermutation_eq`
  -- the doubly programmed view and the shifted game's singly programmed view
  are the two sides of `programmed_programmed_apply_of_ne`: they agree at every
  index outside the steering gate's programmed slots, and at each of those
  indices they are `programmed (programmed π ℓ f) ℓ s` and `programmed π ℓ s`.
* `publicAnswer_steeringFamily` -- the identical-until-bad input for the whole
  family of steering indices, in the `publicAnswer` form `run_idealOracle_agree`
  consumes. A permutation query names one index, so the family version is the
  single-index `publicAnswer_steeringHidden` keyed to the query's own index;
  keying it this way is what lets the union bound cost one charge per log entry
  rather than one per index.

What is left after this file is the probabilistic step: the mass of the bad
event under the joint law of the shifted game and the two hash-fiber chunks.
-/

import Proof.Erased
import Proof.Shifted

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

noncomputable section

/-! ### The steering target on the curve -/

/-- On the curve the simulator's steering target is the hybrid side's bridge key. -/
theorem steeringTarget_onCurve [FieldCertificate] [GroupCertificate] (carrier : NonZeroBase)
    (scalar : NonZeroScalar) (input : AffineInput) (onCurve : curveGap input = 0) :
    steeringTarget carrier input (checkedScalarMultiplication scalar.value input) =
      some (hybridBridge scalar carrier) := by
  have defined : decodePoint input ≠ none :=
    (decodePoint_defined input).mpr ((curveGap_eq_zero_iff input).mp onCurve)
  obtain ⟨point, decoded⟩ := Option.ne_none_iff_exists'.mp defined
  simp only [checkedScalarMultiplication, decoded, Option.map_some, scalarMultiplication,
    steeringTarget, discreteLog_smul (decodePoint_ne_zero input point decoded)]
  rfl

/-! ### The steering request law as one fiber sample -/

/-- The value the steering must force at the steering gate. -/
def steeringWanted (view : View) (table : CurveMembership.Table) (input : AffineInput)
    (mac : InputMac) (target : BaseField) : BaseField :=
  BitAdaptor.evaluate (fixedKeyGate view.1 .x7 0) (table.x7.get 0) (steeringBit input)
      (mac.x.get 0) +
    (target - CurveMembership.evaluate (curveOracles view.1) table input mac)

/-- Both branches of the steering request law sample a fiber of the wanted value: the
`true` branch ignores it. -/
theorem steerRequestLaw_eq_map (view : View) (table : CurveMembership.Table)
    (input : AffineInput) (mac : InputMac) (target : BaseField) :
    steerRequestLaw view table input mac target =
      (uniformHashFiber (steeringWanted view table input mac target)).map
        (steerRequests table (mac.x.get 0) input (steeringWanted view table input mac target)) := by
  unfold steerRequestLaw steerRequests steeringWanted
  simp only
  split
  · exact (PMF.map_const _ _).symm
  · rfl

/-- On the curve the reference view already releases the round's own bridge key, so the
value the steering forces is the steering gate's selected output shifted by the difference
of the two bridge keys. -/
theorem steeringWanted_programSelected (oracle : PermutationOracle FixedKeyIndex Block)
    (bridgeKey : BaseField) (key : InputMacKey) (raw : Coordinates) (input : AffineInput)
    (fibers : GateValues (BitVec 384)) (target : BaseField) (view : View)
    (viewEq : view.1 = programIndices (selectedPrograms key input
      (encodeCoordinates input raw).hash (tableRow (raw.table bridgeKey key)) fibers) oracle)
    (fiberValues : ∀ adaptor position, (((fibers adaptor position).toNat : Nat) : BaseField) =
      (encodeCoordinates input raw).hash adaptor position)
    (onCurve : curveGap input = 0) :
    steeringWanted view (raw.table bridgeKey key) input (key.encodeAffine input) target =
      (encodeCoordinates input raw).hash .x7 0 + (target - bridgeKey) := by
  have released : CurveMembership.evaluate (curveOracles view.1) (raw.table bridgeKey key) input
      (key.encodeAffine input) = bridgeKey := by
    rw [viewEq, curveEvaluate_programSelected oracle bridgeKey key raw input fibers fiberValues,
      onCurve, mul_zero, add_zero]
  have gate : BitAdaptor.evaluate (fixedKeyGate view.1 .x7 0)
      ((raw.table bridgeKey key).x7.get 0) (steeringBit input)
      ((key.encodeAffine input).x.get 0) = (encodeCoordinates input raw).hash .x7 0 := by
    rw [viewEq, steeringBit_eq,
      show ((key.encodeAffine input).x.get 0) = selectedLabel key input .x7 0 from
        gateMac_encodeAffine key input .x7 0]
    exact evaluate_programSelected oracle key input _ _ fibers .x7 0 (fiberValues .x7 0) _ rfl
  rw [steeringWanted, released, gate]

/-! ### The doubly programmed view -/

/-- The view the steered second stage runs on: the unprogrammed permutation family
programmed at the selected labels and then again at the steering gate. -/
def doubleSteeredOracle (key : InputMacKey) (input : AffineInput)
    (outputs : GateValues BaseField) (rows : GateValues BitAdaptor.Ciphertext)
    (fibers : GateValues (BitVec 384)) (wanted : BaseField) (hash : BitVec 384)
    (oracle : PermutationOracle FixedKeyIndex Block) : PermutationOracle FixedKeyIndex Block :=
  programIndices (steerPrograms key input wanted hash (rows .x7 0))
    (programIndices (selectedPrograms key input outputs rows fibers) oracle)

/-- On the curve, and when the steering's own requests are fresh, the steered second stage
is one extra fiber sample followed by the hybrid second stage on the doubly programmed
view. This is the shape the charge compares with the shifted reference round. -/
theorem selectedSimulatedStageTwo_double [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (view : View) (key : InputMacKey) (carrier : NonZeroBase) (bridgeKey : BaseField)
    (raw : Coordinates) (priorLog : List Query) (input : AffineInput)
    (advState : adversary.State) (fibers : GateValues (BitVec 384))
    (fiberValues : ∀ adaptor position, (((fibers adaptor position).toNat : Nat) : BaseField) =
      (encodeCoordinates input raw).hash adaptor position)
    (onCurve : curveGap input = 0)
    (fresh : ∀ hash ∈ (uniformHashFiber ((encodeCoordinates input raw).hash .x7 0 +
        (hybridBridge scalar carrier - bridgeKey))).support,
      ∀ request ∈ steerRequests (raw.table bridgeKey key) (selectedLabel key input .x7 0) input
        ((encodeCoordinates input raw).hash .x7 0 + (hybridBridge scalar carrier - bridgeKey))
        hash,
      request.Fresh priorLog (programIndices (selectedPrograms key input
        (encodeCoordinates input raw).hash (tableRow (raw.table bridgeKey key)) fibers) view.1)) :
    selectedSimulatedStageTwo adversary parameter auxiliary
        (raw.table bridgeKey key, carrierBits carrier) input
        (checkedScalarMultiplication scalar.value input) advState
        (encodeCoordinates input raw).hash fibers
        (stageTwoState view priorLog (raw.table bridgeKey key) carrier key) =
      (uniformHashFiber ((encodeCoordinates input raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey))).bind fun hash =>
        hybridStageTwo adversary parameter auxiliary
          (raw.table bridgeKey key, carrierBits carrier) input advState
          (stageTwoState (doubleSteeredOracle key input (encodeCoordinates input raw).hash
              (tableRow (raw.table bridgeKey key)) fibers
              ((encodeCoordinates input raw).hash .x7 0 +
                (hybridBridge scalar carrier - bridgeKey)) hash view.1, view.2)
            priorLog (raw.table bridgeKey key) carrier key) := by
  set outputs := (encodeCoordinates input raw).hash with outputsDef
  set table := raw.table bridgeKey key with tableDef
  set wanted := outputs .x7 0 + (hybridBridge scalar carrier - bridgeKey) with wantedDef
  set programmedView : View :=
    (programIndices (selectedPrograms key input outputs (tableRow table) fibers) view.1, view.2)
    with programmedViewDef
  have stateEq : programSelected (stageTwoState view priorLog table carrier key) input outputs
      fibers = stageTwoState programmedView priorLog table carrier key :=
    programSelected_stageTwoState view priorLog table carrier key input outputs fibers
  have targetEq : steeringTarget carrier input
      (checkedScalarMultiplication scalar.value input) = some (hybridBridge scalar carrier) :=
    steeringTarget_onCurve carrier scalar input onCurve
  have wantedEq : steeringWanted programmedView table input (key.encodeAffine input)
      (hybridBridge scalar carrier) = wanted :=
    steeringWanted_programSelected view.1 bridgeKey key raw input fibers
      (hybridBridge scalar carrier) programmedView rfl fiberValues onCurve
  show simulatedStageTwo adversary parameter auxiliary (table, carrierBits carrier) input
      (checkedScalarMultiplication scalar.value input) advState
      (programSelected (stageTwoState view priorLog table carrier key) input outputs fibers) = _
  rw [stateEq, simulatedStageTwo_eq,
    simulateRequestLaw_some _ input _ (hybridBridge scalar carrier) targetEq,
    steerRequestLaw_eq_map]
  simp only [stageTwoState_view, stageTwoState_table, stageTwoState_inputMacKey,
    stageTwoState_log, stageTwoState_carrier]
  rw [wantedEq, PMF.bind_map]
  refine bind_congr_support fun hash member => ?_
  have label : ((key.encodeAffine input).x.get 0) = selectedLabel key input .x7 0 :=
    gateMac_encodeAffine key input .x7 0
  rw [label]
  simp only [Function.comp_apply]
  have programmed : programAll (stageTwoState programmedView priorLog table carrier key)
      (steerRequests table (selectedLabel key input .x7 0) input wanted hash) =
      stageTwoState (doubleSteeredOracle key input outputs (tableRow table) fibers wanted hash
        view.1, view.2) priorLog table carrier key :=
    programAll_steerRequests _ key input wanted hash (fresh hash member)
  rw [programmed]
  rfl

/-! ### The double programming against the single one -/

/-- The single programming the shifted reference round performs: the reference programming
of the shifted outputs and the resampled steering fiber, on the unprogrammed family. -/
def shiftedOracle (key : InputMacKey) (input : AffineInput) (outputs : GateValues BaseField)
    (rows : GateValues BitAdaptor.Ciphertext) (fibers : GateValues (BitVec 384))
    (wanted : BaseField) (hash : BitVec 384)
    (oracle : PermutationOracle FixedKeyIndex Block) : PermutationOracle FixedKeyIndex Block :=
  programIndices (selectedPrograms key input (setSteering wanted outputs) rows
    (setSteering hash fibers)) oracle

/-- The queries at which a second programming of already programmed indices differs from
programming those indices once to the second range.

A forward query is hidden when its image under the unprogrammed permutation is one of the
two ranges; an inverse query when its argument is the first range or the image the
programming erases. Both conditions live at the query's **own** index, which is what lets
the union bound charge one log entry once rather than once per tracked index. -/
def doubledHidden (oracle : PermutationOracle FixedKeyIndex Block) (honest steered : Programs) :
    Query → Prop
  | .fixedForward index input =>
      ∃ label first second, honest index = some (label, first) ∧
        steered index = some (label, second) ∧
        (oracle.permutation index input = first ∨ oracle.permutation index input = second)
  | .fixedInverse index value =>
      ∃ label first second, honest index = some (label, first) ∧
        steered index = some (label, second) ∧
        (value = first ∨ value = oracle.permutation index label)
  | _ => False

/-- Off its hidden queries, the doubly programmed family answers as the singly programmed
one. This is the identical-until-bad input of the steering hop, for the whole family of
programmed indices at once. -/
theorem publicAnswer_doubled
    (rest : PermutationOracle Garbling.EncIndex Block × (BaseField → Block × Block))
    (oracle : PermutationOracle FixedKeyIndex Block) (honest steered combined : Programs)
    (untouched : ∀ index, steered index = none → combined index = honest index)
    (covered : ∀ index label second, steered index = some (label, second) →
      ∃ first, honest index = some (label, first))
    (retargeted : ∀ index label second, steered index = some (label, second) →
      combined index = some (label, second))
    (query : Query) (good : ¬ doubledHidden oracle honest steered query) :
    publicAnswer (programIndices steered (programIndices honest oracle), rest) query =
      publicAnswer (programIndices combined oracle, rest) query := by
  cases query with
  | fixedForward index input =>
    show (programIndices steered (programIndices honest oracle)).permutation index input =
      (programIndices combined oracle).permutation index input
    cases steeredAt : steered index with
    | none =>
      rw [programIndices_none steered _ index steeredAt,
        programIndices_congr_at combined honest oracle index (untouched index steeredAt)]
    | some pair =>
      obtain ⟨label, second⟩ := pair
      obtain ⟨first, honestAt⟩ := covered index label second steeredAt
      have bad : ¬(oracle.permutation index input = first ∨
          oracle.permutation index input = second) := fun hit =>
        good ⟨label, first, second, honestAt, steeredAt, hit⟩
      rw [programIndices_eq_programmed steered _ index label second steeredAt,
        programIndices_eq_programmed honest oracle index label first honestAt,
        programIndices_eq_programmed combined oracle index label second
          (retargeted index label second steeredAt)]
      exact programmed_programmed_apply_of_ne (oracle.permutation index) label first second input
        (fun hit => bad (Or.inl hit)) (fun hit => bad (Or.inr hit))
  | fixedInverse index value =>
    show ((programIndices steered (programIndices honest oracle)).permutation index).symm
        value = ((programIndices combined oracle).permutation index).symm value
    cases steeredAt : steered index with
    | none =>
      rw [programIndices_none steered _ index steeredAt,
        programIndices_congr_at combined honest oracle index (untouched index steeredAt)]
    | some pair =>
      obtain ⟨label, second⟩ := pair
      obtain ⟨first, honestAt⟩ := covered index label second steeredAt
      have bad : ¬(value = first ∨ value = oracle.permutation index label) := fun hit =>
        good ⟨label, first, second, honestAt, steeredAt, hit⟩
      rw [programIndices_eq_programmed steered _ index label second steeredAt,
        programIndices_eq_programmed honest oracle index label first honestAt,
        programIndices_eq_programmed combined oracle index label second
          (retargeted index label second steeredAt)]
      exact programmed_programmed_symm_apply_of_ne (oracle.permutation index) label first second
        value (fun hit => bad (Or.inl hit)) (fun hit => bad (Or.inr hit))
  | encForward queryIndex value => rfl
  | encInverse queryIndex value => rfl
  | hash value => rfl

/-- The steering hop's own instance: off the hidden queries, the doubly programmed view of
the steered reference round answers as the singly programmed view of the shifted reference
round. -/
theorem publicAnswer_steeringDouble (key : InputMacKey) (input : AffineInput)
    (outputs : GateValues BaseField) (rows : GateValues BitAdaptor.Ciphertext)
    (fibers : GateValues (BitVec 384)) (wanted : BaseField) (hash : BitVec 384)
    (rest : PermutationOracle Garbling.EncIndex Block × (BaseField → Block × Block))
    (oracle : PermutationOracle FixedKeyIndex Block) (query : Query)
    (good : ¬ doubledHidden oracle (selectedPrograms key input outputs rows fibers)
      (steerPrograms key input wanted hash (rows .x7 0)) query) :
    publicAnswer (doubleSteeredOracle key input outputs rows fibers wanted hash oracle, rest)
        query =
      publicAnswer (shiftedOracle key input outputs rows fibers wanted hash oracle, rest) query :=
  publicAnswer_doubled rest oracle _ _ _
    (steerPrograms_untouched key input outputs (setSteering wanted outputs) rows fibers wanted
      hash fun adaptor position atGate =>
        setSteering_other wanted outputs adaptor position atGate)
    (steerPrograms_covered key input outputs rows fibers wanted hash)
    (steerPrograms_retargeted key input (setSteering wanted outputs) rows fibers wanted hash
      (setSteering_steeringGate wanted outputs))
    query good

/-- The shifted reference round's view, written with the steering shift instead of the
resampled value. -/
theorem shiftedOracle_eq_shiftSteering (key : InputMacKey) (input : AffineInput)
    (outputs : GateValues BaseField) (rows : GateValues BitAdaptor.Ciphertext)
    (fibers : GateValues (BitVec 384)) (shift : BaseField) (hash : BitVec 384)
    (oracle : PermutationOracle FixedKeyIndex Block) :
    shiftedOracle key input outputs rows fibers (outputs .x7 0 + shift) hash oracle =
      programIndices (selectedPrograms key input (shiftSteering shift outputs) rows
        (setSteering hash fibers)) oracle := by
  rw [shiftedOracle, shiftSteering_eq_setSteering]

/-! ### The two second stages under one sample -/

/-- A sampled fiber family realises the selected outputs. -/
theorem fiberValues_of_mem_uniformHashFibers (outputs : GateValues BaseField)
    (fibers : GateValues (BitVec 384)) (member : fibers ∈ (uniformHashFibers outputs).support)
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount) :
    (((fibers adaptor position).toNat : Nat) : BaseField) = outputs adaptor position := by
  rw [uniformHashFibers, PMF.support_map] at member
  obtain ⟨⟨values, property⟩, _, rfl⟩ := member
  exact property adaptor position

/-- The shifted reference round's second stage, with its single fiber sample split into the
honest family and the steering gate's own resample. The split is exact: resampling the
steering gate's fiber on top of the honest family is the fiber family of the shifted
outputs. -/
theorem releasedStageTwo_shifted (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (view : View) (key : InputMacKey) (carrier : NonZeroBase) (table : CurveMembership.Table)
    (outputs : GateValues BaseField) (shift : BaseField)
    (outcome : (AffineInput × adversary.State) × List Query) :
    releasedStageTwo adversary parameter auxiliary view key carrier table
        (shiftSteering shift outputs) outcome =
      (uniformHashFibers outputs).bind fun fibers =>
        (uniformHashFiber (outputs .x7 0 + shift)).bind fun hash =>
          (hybridStageTwo adversary parameter auxiliary (table, carrierBits carrier)
              outcome.1.1 outcome.1.2
              (stageTwoState (shiftedOracle key outcome.1.1 outputs (tableRow table) fibers
                (outputs .x7 0 + shift) hash view.1, view.2) outcome.2 table carrier key)).map
            Prod.fst := by
  rw [releasedStageTwo, shiftSteering_eq_setSteering,
    ← uniformHashFibers_setSteering outputs (outputs .x7 0 + shift), PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun fibers => ?_)
  rw [PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun hash => ?_)
  show (selectedStageTwo adversary parameter auxiliary (table, carrierBits carrier) outcome.1.1
      outcome.1.2 (setSteering (outputs .x7 0 + shift) outputs) (setSteering hash fibers)
      (stageTwoState view outcome.2 table carrier key)).map Prod.fst = _
  rw [selectedStageTwo, programSelected_stageTwoState]
  rfl

/-- The steered reference round's second stage, on the curve and on a good log, with its two
fiber samples written as the honest family and the steering gate's resample -- the same two
samples as the shifted round, in the same order. The only difference between the two second
stages is now the view: doubly programmed here, singly programmed there. -/
theorem steeredReleasedStageTwo_double [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (view : View) (key : InputMacKey) (carrier : NonZeroBase) (bridgeKey : BaseField)
    (raw : Coordinates) (outcome : (AffineInput × adversary.State) × List Query)
    (onCurve : curveGap outcome.1.1 = 0)
    (fresh : ∀ fibers ∈ (uniformHashFibers (encodeCoordinates outcome.1.1 raw).hash).support,
      ∀ hash ∈ (uniformHashFiber ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
        (hybridBridge scalar carrier - bridgeKey))).support,
      ∀ request ∈ steerRequests (raw.table bridgeKey key)
        (selectedLabel key outcome.1.1 .x7 0) outcome.1.1
        ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey)) hash,
      request.Fresh outcome.2 (programIndices (selectedPrograms key outcome.1.1
        (encodeCoordinates outcome.1.1 raw).hash (tableRow (raw.table bridgeKey key)) fibers)
        view.1)) :
    steeredReleasedStageTwo scalar adversary parameter auxiliary view key carrier
        (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash outcome =
      (uniformHashFibers (encodeCoordinates outcome.1.1 raw).hash).bind fun fibers =>
        (uniformHashFiber ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
            (hybridBridge scalar carrier - bridgeKey))).bind fun hash =>
          (hybridStageTwo adversary parameter auxiliary
              (raw.table bridgeKey key, carrierBits carrier) outcome.1.1 outcome.1.2
              (stageTwoState (doubleSteeredOracle key outcome.1.1
                (encodeCoordinates outcome.1.1 raw).hash (tableRow (raw.table bridgeKey key))
                fibers ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                  (hybridBridge scalar carrier - bridgeKey)) hash view.1, view.2)
                outcome.2 (raw.table bridgeKey key) carrier key)).map Prod.fst := by
  rw [steeredReleasedStageTwo]
  refine bind_congr_support fun fibers member => ?_
  rw [selectedSimulatedStageTwo_double scalar adversary parameter auxiliary view key carrier
    bridgeKey raw outcome.2 outcome.1.1 outcome.1.2 fibers
    (fiberValues_of_mem_uniformHashFibers _ fibers member) onCurve (fresh fibers member),
    PMF.map_bind]

/-- The two second stages agree at every outcome whose log avoids the hidden queries. This
is the identical-until-bad statement of the steering hop: what is left of step 7 is the mass
of the logs that do not avoid them, plus the mass of the steering requests that are not
fresh. -/
theorem hybridStageTwo_doubled_agree (adversary : Adversary) (parameter : Nat)
    (auxiliary : Unit) (circuit : Garbling.Public) (input : AffineInput)
    (advState : adversary.State) (key : InputMacKey) (outputs : GateValues BaseField)
    (rows : GateValues BitAdaptor.Ciphertext) (fibers : GateValues (BitVec 384))
    (wanted : BaseField) (hash : BitVec 384) (view : View) (priorLog : List Query)
    (table : CurveMembership.Table) (carrier : NonZeroBase) (result : Bool) (log : List Query)
    (good : ∀ query ∈ log, ¬ doubledHidden view.1
      (selectedPrograms key input outputs rows fibers)
      (steerPrograms key input wanted hash (rows .x7 0)) query) :
    hybridStageTwo adversary parameter auxiliary circuit input advState
        (stageTwoState (doubleSteeredOracle key input outputs rows fibers wanted hash view.1,
          view.2) priorLog table carrier key) (result, log) =
      hybridStageTwo adversary parameter auxiliary circuit input advState
        (stageTwoState (shiftedOracle key input outputs rows fibers wanted hash view.1, view.2)
          priorLog table carrier key) (result, log) := by
  refine run_idealOracle_agree _ _
    (stageTwoState (doubleSteeredOracle key input outputs rows fibers wanted hash view.1, view.2)
      priorLog table carrier key)
    (stageTwoState (shiftedOracle key input outputs rows fibers wanted hash view.1, view.2)
      priorLog table carrier key)
    rfl (fun query goodQuery => ?_) result log good
  exact publicAnswer_steeringDouble key input outputs rows fibers wanted hash view.2 view.1 query
    goodQuery

/-! ### The freshness half of the bad event -/

/-- The queries that block the steering's own programming.

The simulator programs a request only when none of the four answers it changes has been
logged (`ProgramRequest.Fresh`). Each of the four is a condition on one query at the
request's **own** index: a forward query at the request's domain or at the preimage of its
range, an inverse query at its range or at the current image of its domain. Keying the
predicate to the query's index this way is what lets the union bound charge one log entry
once rather than once per steering slot. -/
def freshnessHidden (view : PermutationOracle FixedKeyIndex Block)
    (requests : List ProgramRequest) : Query → Prop
  | .fixedForward index input =>
      ∃ request ∈ requests, request.index = index ∧
        (input = request.domain ∨ view.permutation index input = request.range)
  | .fixedInverse index value =>
      ∃ request ∈ requests, request.index = index ∧
        (value = request.range ∨ value = view.permutation index request.domain)
  | _ => False

/-- Off the blocking queries, every request of the steering is fresh. This is the
identical-until-bad input for the freshness half of the steering hop's bad event: it turns
the abstract `fresh` hypothesis of `selectedSimulatedStageTwo_double` into a condition on
the entries of the first stage's log. -/
theorem fresh_of_notMem_freshnessHidden (view : PermutationOracle FixedKeyIndex Block)
    (requests : List ProgramRequest) (log : List Query)
    (good : ∀ query ∈ log, ¬ freshnessHidden view requests query)
    (request : ProgramRequest) (member : request ∈ requests) :
    request.Fresh log view := by
  refine ⟨fun logged => good _ logged ⟨request, member, rfl, Or.inl rfl⟩,
    fun logged => good _ logged ⟨request, member, rfl, Or.inr ?_⟩,
    fun logged => good _ logged ⟨request, member, rfl, Or.inl rfl⟩,
    fun logged => good _ logged ⟨request, member, rfl, Or.inr rfl⟩⟩
  exact Equiv.apply_symm_apply _ _

/-- The transcript conditions of the double programming already imply the steering's own
freshness: a first stage that has neither queried the selected label nor used either
programmed range cannot have logged any of the four answers the steering changes.

So the freshness half of the steering hop's bad event is **not** a separate charge. The
fourth clause -- no forward entry whose programmed image is the steered range -- is the one
that needs the transcript: a logged forward entry is pinned, the honest programming moves
only the erased image and the honest range, and the transcript uses neither. -/
theorem not_freshnessHidden_of_covers (index : FixedKeyIndex) (assign : Assignment)
    (permutation : Equiv Block Block) (compatible : Compatible assign permutation)
    (label honest steered : Block) (fresh : assign label = none)
    (honestUnused : honest ∉ pinnedRange assign) (steeredUnused : steered ∉ pinnedRange assign)
    (log : List Query) (covers : TranscriptCovers index assign log)
    (view : PermutationOracle FixedKeyIndex Block)
    (atIndex : view.permutation index = programmed permutation label honest)
    (query : Query) (member : query ∈ log) :
    ¬ freshnessHidden view [⟨index, label, steered⟩] query := by
  cases query with
  | fixedForward queryIndex input =>
    rintro ⟨request, requestMember, requestIndex, hit⟩
    rw [List.mem_singleton] at requestMember
    subst requestMember
    subst requestIndex
    obtain ⟨value, pinned⟩ := Option.isSome_iff_exists.mp (covers.1 input member)
    rcases hit with atLabel | atRange
    · rw [atLabel, fresh] at pinned
      exact absurd pinned (by simp)
    · have notHonest : value ≠ honest := fun same =>
        honestUnused (mem_pinnedRange (same ▸ pinned))
      have notErased : value ≠ permutation label := by
        intro same
        have sameInput : input = label :=
          permutation.injective ((compatible input value pinned).trans same)
        rw [sameInput, fresh] at pinned
        exact absurd pinned (by simp)
      rw [atIndex, programmed_apply, compatible input value pinned,
        Equiv.swap_apply_of_ne_of_ne notErased notHonest] at atRange
      exact steeredUnused (mem_pinnedRange (atRange ▸ pinned))
  | fixedInverse queryIndex value =>
    rintro ⟨request, requestMember, requestIndex, hit⟩
    rw [List.mem_singleton] at requestMember
    subst requestMember
    subst requestIndex
    rcases hit with atRange | atErased
    · have valueEq : value = steered := atRange
      exact steeredUnused (valueEq ▸ covers.2 value member)
    · rw [atIndex, programmed_apply_label] at atErased
      exact honestUnused (atErased ▸ covers.2 value member)
  | encForward queryIndex value => exact fun hidden => hidden
  | encInverse queryIndex value => exact fun hidden => hidden
  | hash value => exact fun hidden => hidden

end

end Kriterion.ArgoMAC.Security
