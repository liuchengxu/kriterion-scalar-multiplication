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

end

end Kriterion.ArgoMAC.Security
