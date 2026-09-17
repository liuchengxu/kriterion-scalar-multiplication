/-
This file is the **one hop** of the steering charge: conditionally on the first
stage's transcripts, the steered reference game's second stage and the shifted
reference game's second stage are the *same law*, unless the selected label is
one of the values those transcripts block.

The two ingredients are already machine-checked. `Proof/Charge.lean` rewrites
both second stages into the same shape -- the honest fiber family, the steering
gate's resample, and then the hybrid second stage on a view that is programmed
either twice (steered) or once (shifted). `Proof/Family.lean` supplies the law
equality of those two views at **every** programmed index at once
(`familyLaw_double`), so the hop is a single application and the accounting is
the sum of the per-index pinned counts.

What this file adds is the bridge from the transcript conditions to the two
side conditions the rewriting needs:

* the steering's own requests are fresh against the first stage's log
  (`steerRequests_fresh_of_covers`), which is `not_freshnessHidden_of_covers`
  applied per request -- the freshness half of the bad event is **not** a
  separate charge;
* the two fiber samples are independent of the permutation family, so they
  commute past it (`PMF.bind_comm`) and the law equality applies pointwise in
  them.

Off the curve the hop is free: the steering has no target, and the shifted
outputs are the honest ones.
-/

import Proof.Charge
import Proof.Family

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

noncomputable section

/-! ### A request list of distinct indices programs each of its own requests -/

/-- A request at a distinct index is the partial programming's own request at that index. -/
theorem programsOfRequests_of_mem (requests : List ProgramRequest)
    (distinct : requests.Pairwise fun first second => first.index ≠ second.index)
    (request : ProgramRequest) (member : request ∈ requests) :
    programsOfRequests requests request.index = some (request.domain, request.range) := by
  induction requests with
  | nil => exact absurd member (by simp)
  | cons head rest inductionHypothesis =>
    obtain ⟨headDistinct, restDistinct⟩ := List.pairwise_cons.mp distinct
    rcases List.mem_cons.mp member with same | tail
    · rw [same, programsOfRequests_cons, if_pos rfl]
    · rw [programsOfRequests_cons,
        if_neg fun equal => headDistinct request tail equal.symm]
      exact inductionHypothesis restDistinct tail

/-! ### The freshness half is free -/

/-- Off the labels the transcripts block, every steering request is fresh against the first
stage's log.

This is `not_freshnessHidden_of_covers` applied once per request: the transcript of the
request's own index has neither queried the selected label nor used either range, and a lazy
run pins every tracked query its log records, so none of the four answers the request changes
can have been logged. -/
theorem steerRequests_fresh_of_covers (key : InputMacKey) (input : AffineInput)
    (table : CurveMembership.Table) (outputs : GateValues BaseField)
    (fibers : GateValues (BitVec 384)) (wanted : BaseField) (hash : BitVec 384)
    (oracle : PermutationOracle FixedKeyIndex Block) (assigns : FamilyAssignment)
    (compatible : ∀ index, Compatible (assigns index) (oracle.permutation index))
    (log : List Query) (covers : FamilyCovers assigns log)
    (good : ¬ steeringBlocked assigns (selectedPrograms key input outputs (tableRow table) fibers)
      (steerPrograms key input wanted hash (tableRow table .x7 0)))
    (request : ProgramRequest)
    (member : request ∈ steerRequests table (selectedLabel key input .x7 0) input wanted hash) :
    request.Fresh log
      (programIndices (selectedPrograms key input outputs (tableRow table) fibers) oracle) := by
  have steeredAt : steerPrograms key input wanted hash (tableRow table .x7 0) request.index =
      some (request.domain, request.range) := by
    rw [← programsOfRequests_steerRequests key input table wanted hash]
    exact programsOfRequests_of_mem _
      (steerRequests_distinct table (selectedLabel key input .x7 0) input wanted hash) request
      member
  obtain ⟨first, honestAt⟩ := steerPrograms_covered key input outputs (tableRow table) fibers
    wanted hash request.index request.domain request.range steeredAt
  obtain ⟨labelFresh, firstUnused, secondUnused⟩ := good_of_not_steeringBlocked assigns _ _ good
    request.index request.domain first request.range honestAt steeredAt
  have atIndex : (programIndices (selectedPrograms key input outputs (tableRow table) fibers)
        oracle).permutation request.index =
      programmed (oracle.permutation request.index) request.domain first :=
    programIndices_eq_programmed _ oracle request.index request.domain first honestAt
  refine fresh_of_notMem_freshnessHidden _ [request] log (fun query queryMember => ?_) request
    (List.mem_singleton_self request)
  exact not_freshnessHidden_of_covers request.index (assigns request.index)
    (oracle.permutation request.index) (compatible request.index) request.domain first
    request.range labelFresh firstUnused secondUnused log (covers request.index) _ atIndex query
    queryMember

/-! ### The two fiber samples commute past the permutation family -/

/-- The permutation family is independent of the two fiber samples, so it may be sampled
after them. -/
theorem familyLaw_bind_fibers_comm (assigns : FamilyAssignment)
    (outputs : GateValues BaseField) (value : BaseField)
    (step : PermutationOracle FixedKeyIndex Block → GateValues (BitVec 384) → BitVec 384 →
      PMF Bool) :
    ((familyLaw assigns).bind fun oracle =>
        (uniformHashFibers outputs).bind fun fibers =>
          (uniformHashFiber value).bind fun hash => step oracle fibers hash) =
      (uniformHashFibers outputs).bind fun fibers =>
        (uniformHashFiber value).bind fun hash =>
          (familyLaw assigns).bind fun oracle => step oracle fibers hash := by
  rw [PMF.bind_comm (familyLaw assigns) (uniformHashFibers outputs)
    fun oracle fibers => (uniformHashFiber value).bind fun hash => step oracle fibers hash]
  refine congrArg (PMF.bind _) (funext fun fibers => ?_)
  exact PMF.bind_comm (familyLaw assigns) (uniformHashFiber value)
    fun oracle hash => step oracle fibers hash

/-! ### The hop -/

/-- The charge of the steering hop, as a law equality conditioned on the first stage's
transcripts.

Given the transcripts of a first stage -- injective, covering their own log, and blocking
none of the labels the steering programs -- the steered reference game's second stage and
the shifted reference game's second stage are the **same law**. There is no residual
second-stage charge of any kind: whatever the second stage queries, and in either branch of
the steering bit, it cannot separate the doubly programmed view from the singly programmed
one.

Off the curve the equality is unconditional. -/
theorem bind_familyLaw_steeredReleased_eq [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (rest : PermutationOracle Garbling.EncIndex Block × (BN254.BaseField → Block × Block))
    (key : InputMacKey) (carrier : NonZeroBase) (bridgeKey : BaseField) (raw : Coordinates)
    (outcome : (AffineInput × adversary.State) × List Query) (assigns : FamilyAssignment)
    (injective : FamilyInjective assigns) (covers : FamilyCovers assigns outcome.2)
    (good : ∀ fibers ∈ (uniformHashFibers (encodeCoordinates outcome.1.1 raw).hash).support,
      ∀ hash ∈ (uniformHashFiber ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey))).support,
        ¬ steeringBlocked assigns
          (selectedPrograms key outcome.1.1 (encodeCoordinates outcome.1.1 raw).hash
            (tableRow (raw.table bridgeKey key)) fibers)
          (steerPrograms key outcome.1.1 ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
              (hybridBridge scalar carrier - bridgeKey)) hash
            (tableRow (raw.table bridgeKey key) .x7 0))) :
    ((familyLaw assigns).bind fun oracle =>
        steeredReleasedStageTwo scalar adversary parameter auxiliary (oracle, rest) key carrier
          (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash outcome) =
      (familyLaw assigns).bind fun oracle =>
        releasedStageTwo adversary parameter auxiliary (oracle, rest) key carrier
          (raw.table bridgeKey key)
          (shiftedOutputs scalar (fun _ => bridgeKey) carrier outcome.1.1
            (encodeCoordinates outcome.1.1 raw).hash) outcome := by
  by_cases onCurve : curveGap outcome.1.1 = 0
  · have shifted : shiftedOutputs scalar (fun _ => bridgeKey) carrier outcome.1.1
        (encodeCoordinates outcome.1.1 raw).hash =
        shiftSteering (hybridBridge scalar carrier - bridgeKey)
          (encodeCoordinates outcome.1.1 raw).hash := by
      rw [shiftedOutputs, if_pos onCurve]
    rw [shifted]
    have left : ((familyLaw assigns).bind fun oracle =>
          steeredReleasedStageTwo scalar adversary parameter auxiliary (oracle, rest) key carrier
            (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash outcome) =
        (familyLaw assigns).bind fun oracle =>
          (uniformHashFibers (encodeCoordinates outcome.1.1 raw).hash).bind fun fibers =>
            (uniformHashFiber ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                (hybridBridge scalar carrier - bridgeKey))).bind fun hash =>
              (hybridStageTwo adversary parameter auxiliary
                  (raw.table bridgeKey key, carrierBits carrier) outcome.1.1 outcome.1.2
                  (stageTwoState (doubleSteeredOracle key outcome.1.1
                    (encodeCoordinates outcome.1.1 raw).hash
                    (tableRow (raw.table bridgeKey key)) fibers
                    ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                      (hybridBridge scalar carrier - bridgeKey)) hash oracle, rest)
                    outcome.2 (raw.table bridgeKey key) carrier key)).map Prod.fst := by
      refine bind_congr_support fun oracle member => ?_
      refine steeredReleasedStageTwo_double scalar adversary parameter auxiliary (oracle, rest)
        key carrier bridgeKey raw outcome onCurve ?_
      intro fibers fibersMember hash hashMember request requestMember
      exact steerRequests_fresh_of_covers key outcome.1.1 (raw.table bridgeKey key)
        (encodeCoordinates outcome.1.1 raw).hash fibers
        ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey)) hash oracle assigns
        (familyLaw_support assigns injective member) outcome.2 covers
        (good fibers fibersMember hash hashMember) request requestMember
    have right : ((familyLaw assigns).bind fun oracle =>
          releasedStageTwo adversary parameter auxiliary (oracle, rest) key carrier
            (raw.table bridgeKey key)
            (shiftSteering (hybridBridge scalar carrier - bridgeKey)
              (encodeCoordinates outcome.1.1 raw).hash) outcome) =
        (familyLaw assigns).bind fun oracle =>
          (uniformHashFibers (encodeCoordinates outcome.1.1 raw).hash).bind fun fibers =>
            (uniformHashFiber ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                (hybridBridge scalar carrier - bridgeKey))).bind fun hash =>
              (hybridStageTwo adversary parameter auxiliary
                  (raw.table bridgeKey key, carrierBits carrier) outcome.1.1 outcome.1.2
                  (stageTwoState (shiftedOracle key outcome.1.1
                    (encodeCoordinates outcome.1.1 raw).hash
                    (tableRow (raw.table bridgeKey key)) fibers
                    ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                      (hybridBridge scalar carrier - bridgeKey)) hash oracle, rest)
                    outcome.2 (raw.table bridgeKey key) carrier key)).map Prod.fst :=
      congrArg (PMF.bind _) (funext fun oracle =>
        releasedStageTwo_shifted adversary parameter auxiliary (oracle, rest) key carrier
          (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash
          (hybridBridge scalar carrier - bridgeKey) outcome)
    rw [left, right,
      familyLaw_bind_fibers_comm assigns (encodeCoordinates outcome.1.1 raw).hash
        ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey))
        (fun oracle fibers hash =>
          (hybridStageTwo adversary parameter auxiliary
              (raw.table bridgeKey key, carrierBits carrier) outcome.1.1 outcome.1.2
              (stageTwoState (doubleSteeredOracle key outcome.1.1
                (encodeCoordinates outcome.1.1 raw).hash (tableRow (raw.table bridgeKey key))
                fibers ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                  (hybridBridge scalar carrier - bridgeKey)) hash oracle, rest)
                outcome.2 (raw.table bridgeKey key) carrier key)).map Prod.fst),
      familyLaw_bind_fibers_comm assigns (encodeCoordinates outcome.1.1 raw).hash
        ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey))
        (fun oracle fibers hash =>
          (hybridStageTwo adversary parameter auxiliary
              (raw.table bridgeKey key, carrierBits carrier) outcome.1.1 outcome.1.2
              (stageTwoState (shiftedOracle key outcome.1.1
                (encodeCoordinates outcome.1.1 raw).hash (tableRow (raw.table bridgeKey key))
                fibers ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                  (hybridBridge scalar carrier - bridgeKey)) hash oracle, rest)
                outcome.2 (raw.table bridgeKey key) carrier key)).map Prod.fst)]
    refine bind_congr_support fun fibers fibersMember => ?_
    refine bind_congr_support fun hash hashMember => ?_
    exact familyLaw_double assigns injective
      (selectedPrograms key outcome.1.1 (encodeCoordinates outcome.1.1 raw).hash
        (tableRow (raw.table bridgeKey key)) fibers)
      (steerPrograms key outcome.1.1 ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey)) hash
        (tableRow (raw.table bridgeKey key) .x7 0))
      (selectedPrograms key outcome.1.1
        (setSteering ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey)) (encodeCoordinates outcome.1.1 raw).hash)
        (tableRow (raw.table bridgeKey key))
        (setSteering hash fibers))
      (fun index steeredNone => steerPrograms_untouched key outcome.1.1
        (encodeCoordinates outcome.1.1 raw).hash
        (setSteering ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey)) (encodeCoordinates outcome.1.1 raw).hash)
        (tableRow (raw.table bridgeKey key)) fibers _ hash
        (fun adaptor position atGate => setSteering_other _ _ adaptor position atGate) index
        steeredNone)
      (steerPrograms_covered key outcome.1.1 (encodeCoordinates outcome.1.1 raw).hash
        (tableRow (raw.table bridgeKey key)) fibers _ hash)
      (steerPrograms_retargeted key outcome.1.1
        (setSteering ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey)) (encodeCoordinates outcome.1.1 raw).hash)
        (tableRow (raw.table bridgeKey key)) fibers _ hash
        (setSteering_steeringGate _ _))
      (good_of_not_steeringBlocked assigns _ _ (good fibers fibersMember hash hashMember))
      (fun view => (hybridStageTwo adversary parameter auxiliary
          (raw.table bridgeKey key, carrierBits carrier) outcome.1.1 outcome.1.2
          (stageTwoState (view, rest) outcome.2 (raw.table bridgeKey key) carrier key)).map
        Prod.fst)
  · have shifted : shiftedOutputs scalar (fun _ => bridgeKey) carrier outcome.1.1
        (encodeCoordinates outcome.1.1 raw).hash = (encodeCoordinates outcome.1.1 raw).hash := by
      rw [shiftedOutputs, if_neg onCurve]
    rw [shifted]
    exact congrArg (PMF.bind _) (funext fun oracle =>
      steeredReleasedStageTwo_offCurve scalar adversary parameter auxiliary (oracle, rest) key
        carrier (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash outcome
        onCurve)

/-! ### The hop at full granularity: the two fiber samples in the sample -/

/-- The steered second stage with its steering fiber exposed, and **no** freshness side
condition: the steering already samples a fiber of the wanted value and then programs, and
the wanted value is the steering gate's shifted output.

Exposing the sample before the freshness step is what lets the charge put both fiber samples
into the sample space of the hop. That order is forced: the steered range is a chunk of this
very sample, so the bad event mentions it, while the selected label -- the variable the bad
event is charged over -- has to be sampled *after* it. -/
theorem selectedSimulatedStageTwo_programAll [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (view : View) (key : InputMacKey) (carrier : NonZeroBase) (bridgeKey : BaseField)
    (raw : Coordinates) (priorLog : List Query) (input : AffineInput)
    (advState : adversary.State) (fibers : GateValues (BitVec 384))
    (fiberValues : ∀ adaptor position, (((fibers adaptor position).toNat : Nat) : BaseField) =
      (encodeCoordinates input raw).hash adaptor position)
    (onCurve : curveGap input = 0) :
    selectedSimulatedStageTwo adversary parameter auxiliary
        (raw.table bridgeKey key, carrierBits carrier) input
        (checkedScalarMultiplication scalar.value input) advState
        (encodeCoordinates input raw).hash fibers
        (stageTwoState view priorLog (raw.table bridgeKey key) carrier key) =
      (uniformHashFiber ((encodeCoordinates input raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey))).bind fun hash =>
        hybridStageTwo adversary parameter auxiliary
          (raw.table bridgeKey key, carrierBits carrier) input advState
          (programAll (stageTwoState (programIndices (selectedPrograms key input
              (encodeCoordinates input raw).hash (tableRow (raw.table bridgeKey key)) fibers)
              view.1, view.2) priorLog (raw.table bridgeKey key) carrier key)
            (steerRequests (raw.table bridgeKey key) (selectedLabel key input .x7 0) input
              ((encodeCoordinates input raw).hash .x7 0 +
                (hybridBridge scalar carrier - bridgeKey)) hash)) := by
  have stateEq : programSelected
      (stageTwoState view priorLog (raw.table bridgeKey key) carrier key) input
      (encodeCoordinates input raw).hash fibers =
      stageTwoState (programIndices (selectedPrograms key input
        (encodeCoordinates input raw).hash (tableRow (raw.table bridgeKey key)) fibers) view.1,
        view.2) priorLog (raw.table bridgeKey key) carrier key :=
    programSelected_stageTwoState view priorLog (raw.table bridgeKey key) carrier key input
      (encodeCoordinates input raw).hash fibers
  have targetEq : steeringTarget carrier input
      (checkedScalarMultiplication scalar.value input) = some (hybridBridge scalar carrier) :=
    steeringTarget_onCurve carrier scalar input onCurve
  have wantedEq : steeringWanted (programIndices (selectedPrograms key input
        (encodeCoordinates input raw).hash (tableRow (raw.table bridgeKey key)) fibers) view.1,
      view.2) (raw.table bridgeKey key) input (key.encodeAffine input)
      (hybridBridge scalar carrier) =
      (encodeCoordinates input raw).hash .x7 0 + (hybridBridge scalar carrier - bridgeKey) :=
    steeringWanted_programSelected view.1 bridgeKey key raw input fibers
      (hybridBridge scalar carrier) _ rfl fiberValues onCurve
  show simulatedStageTwo adversary parameter auxiliary
      (raw.table bridgeKey key, carrierBits carrier) input
      (checkedScalarMultiplication scalar.value input) advState
      (programSelected (stageTwoState view priorLog (raw.table bridgeKey key) carrier key) input
        (encodeCoordinates input raw).hash fibers) = _
  rw [stateEq, simulatedStageTwo_eq,
    simulateRequestLaw_some _ input _ (hybridBridge scalar carrier) targetEq,
    steerRequestLaw_eq_map]
  simp only [stageTwoState_view, stageTwoState_table, stageTwoState_inputMacKey]
  rw [wantedEq, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun hash => ?_)
  simp only [Function.comp_apply]
  rw [show ((key.encodeAffine input).x.get 0) = selectedLabel key input .x7 0 from
    gateMac_encodeAffine key input .x7 0]
  simp only [hybridStageTwo, programAll_inputMacKey, stageTwoState_inputMacKey]

/-- The steered reference second stage with both fiber samples exposed, unconditionally on
the curve. -/
theorem steeredReleasedStageTwo_programAll [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (view : View) (key : InputMacKey) (carrier : NonZeroBase) (bridgeKey : BaseField)
    (raw : Coordinates) (outcome : (AffineInput × adversary.State) × List Query)
    (onCurve : curveGap outcome.1.1 = 0) :
    steeredReleasedStageTwo scalar adversary parameter auxiliary view key carrier
        (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash outcome =
      (uniformHashFibers (encodeCoordinates outcome.1.1 raw).hash).bind fun fibers =>
        (uniformHashFiber ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
            (hybridBridge scalar carrier - bridgeKey))).bind fun hash =>
          (hybridStageTwo adversary parameter auxiliary
              (raw.table bridgeKey key, carrierBits carrier) outcome.1.1 outcome.1.2
              (programAll (stageTwoState (programIndices (selectedPrograms key outcome.1.1
                  (encodeCoordinates outcome.1.1 raw).hash
                  (tableRow (raw.table bridgeKey key)) fibers) view.1, view.2)
                outcome.2 (raw.table bridgeKey key) carrier key)
                (steerRequests (raw.table bridgeKey key) (selectedLabel key outcome.1.1 .x7 0)
                  outcome.1.1 ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                    (hybridBridge scalar carrier - bridgeKey)) hash))).map Prod.fst := by
  rw [steeredReleasedStageTwo]
  refine bind_congr_support fun fibers member => ?_
  rw [selectedSimulatedStageTwo_programAll scalar adversary parameter auxiliary view key carrier
    bridgeKey raw outcome.2 outcome.1.1 outcome.1.2 fibers
    (fiberValues_of_mem_uniformHashFibers _ fibers member) onCurve, PMF.map_bind]

/-- **The hop, at the granularity the charge consumes.** With the two fiber samples and the
selected label already fixed, and the transcripts blocking none of the labels the steering
programs, the steered second stage and the shifted second stage are the same law.

The freshness step is inside the good region (it needs the transcript conditions for the
given sample), and the law equality is one application of `familyLaw_double` over all the
programmed indices at once. -/
theorem bind_familyLaw_programAll_eq_shifted (adversary : Adversary) (parameter : Nat)
    (auxiliary : Unit)
    (rest : PermutationOracle Garbling.EncIndex Block × (BN254.BaseField → Block × Block))
    (key : InputMacKey) (carrier : NonZeroBase) (table : CurveMembership.Table)
    (input : AffineInput) (advState : adversary.State) (log : List Query)
    (outputs : GateValues BaseField) (fibers : GateValues (BitVec 384)) (wanted : BaseField)
    (hash : BitVec 384) (assigns : FamilyAssignment) (injective : FamilyInjective assigns)
    (covers : FamilyCovers assigns log)
    (good : ¬ steeringBlocked assigns
      (selectedPrograms key input outputs (tableRow table) fibers)
      (steerPrograms key input wanted hash (tableRow table .x7 0))) :
    ((familyLaw assigns).bind fun oracle =>
        (hybridStageTwo adversary parameter auxiliary (table, carrierBits carrier) input advState
            (programAll (stageTwoState (programIndices (selectedPrograms key input outputs
                (tableRow table) fibers) oracle, rest) log table carrier key)
              (steerRequests table (selectedLabel key input .x7 0) input wanted hash))).map
          Prod.fst) =
      (familyLaw assigns).bind fun oracle =>
        (hybridStageTwo adversary parameter auxiliary (table, carrierBits carrier) input advState
            (stageTwoState (shiftedOracle key input outputs (tableRow table) fibers wanted hash
              oracle, rest) log table carrier key)).map Prod.fst := by
  have step : ((familyLaw assigns).bind fun oracle =>
        (hybridStageTwo adversary parameter auxiliary (table, carrierBits carrier) input advState
            (programAll (stageTwoState (programIndices (selectedPrograms key input outputs
                (tableRow table) fibers) oracle, rest) log table carrier key)
              (steerRequests table (selectedLabel key input .x7 0) input wanted hash))).map
          Prod.fst) =
      (familyLaw assigns).bind fun oracle =>
        (hybridStageTwo adversary parameter auxiliary (table, carrierBits carrier) input advState
            (stageTwoState (doubleSteeredOracle key input outputs (tableRow table) fibers wanted
              hash oracle, rest) log table carrier key)).map Prod.fst := by
    refine bind_congr_support fun oracle member => ?_
    have programmed : programAll (stageTwoState (programIndices (selectedPrograms key input
            outputs (tableRow table) fibers) oracle, rest) log table carrier key)
          (steerRequests table (selectedLabel key input .x7 0) input wanted hash) =
        stageTwoState (doubleSteeredOracle key input outputs (tableRow table) fibers wanted hash
          oracle, rest) log table carrier key :=
      programAll_steerRequests _ key input wanted hash fun request requestMember =>
        steerRequests_fresh_of_covers key input table outputs fibers wanted hash oracle assigns
          (familyLaw_support assigns injective member) log covers good request requestMember
    rw [programmed]
  rw [step]
  exact familyLaw_double assigns injective
    (selectedPrograms key input outputs (tableRow table) fibers)
    (steerPrograms key input wanted hash (tableRow table .x7 0))
    (selectedPrograms key input (setSteering wanted outputs) (tableRow table)
      (setSteering hash fibers))
    (fun index steeredNone => steerPrograms_untouched key input outputs
      (setSteering wanted outputs) (tableRow table) fibers wanted hash
      (fun adaptor position atGate => setSteering_other wanted outputs adaptor position atGate)
      index steeredNone)
    (steerPrograms_covered key input outputs (tableRow table) fibers wanted hash)
    (steerPrograms_retargeted key input (setSteering wanted outputs) (tableRow table) fibers
      wanted hash (setSteering_steeringGate wanted outputs))
    (good_of_not_steeringBlocked assigns _ _ good)
    (fun oracleView => (hybridStageTwo adversary parameter auxiliary
        (table, carrierBits carrier) input advState
        (stageTwoState (oracleView, rest) log table carrier key)).map Prod.fst)

/-! ### The bad event of the hop, priced over the selected label -/

/-- The chunk the reference programming installs at an index: the programmed range with the
selected label removed. -/
def selectedChunk (outputs : GateValues BaseField) (rows : GateValues BitAdaptor.Ciphertext)
    (fibers : GateValues (BitVec 384)) (index : FixedKeyIndex) : Block :=
  slotChunk index.slot (fibers index.adaptor index.position)
    (rows index.adaptor index.position ^^^
      BitAdaptor.fieldBytes (outputs index.adaptor index.position))

/-- The chunk the steering installs at an index. -/
def steeredChunk (row : BitAdaptor.Ciphertext) (wanted : BaseField) (hash : BitVec 384)
    (index : FixedKeyIndex) : Block :=
  slotChunk index.slot hash (BitAdaptor.fieldBytes wanted ^^^ row)

theorem selectedPrograms_range (key : InputMacKey) (input : AffineInput)
    (outputs : GateValues BaseField) (rows : GateValues BitAdaptor.Ciphertext)
    (fibers : GateValues (BitVec 384)) (index : FixedKeyIndex) (label range : Block)
    (requested : selectedPrograms key input outputs rows fibers index = some (label, range)) :
    range = selectedChunk outputs rows fibers index ^^^ label := by
  obtain ⟨adaptor, position, slot⟩ := index
  cases slot with
  | hash chunk =>
    rw [selectedPrograms_hash] at requested
    cases bit : inputBits input adaptor position with
    | true => rw [bit, if_pos rfl] at requested; exact absurd requested (by simp)
    | false =>
      rw [bit, if_neg Bool.false_ne_true] at requested
      have parts : selectedLabel key input adaptor position = label ∧
          slotRange (.hash chunk) (fibers adaptor position) 0
            (selectedLabel key input adaptor position) = range := by simpa using requested
      rw [← parts.2, slotRange_eq_slotChunk, parts.1]
      rfl
  | pad chunk =>
    rw [selectedPrograms_pad] at requested
    cases bit : inputBits input adaptor position with
    | false => rw [bit, if_neg Bool.false_ne_true] at requested; exact absurd requested (by simp)
    | true =>
      rw [bit, if_pos rfl] at requested
      have parts : selectedLabel key input adaptor position = label ∧
          slotRange (.pad chunk) 0
            (rows adaptor position ^^^ BitAdaptor.fieldBytes (outputs adaptor position))
            (selectedLabel key input adaptor position) = range := by simpa using requested
      rw [← parts.2, slotRange_eq_slotChunk, parts.1]
      rfl

theorem steerPrograms_range (key : InputMacKey) (input : AffineInput) (wanted : BaseField)
    (hash : BitVec 384) (row : BitAdaptor.Ciphertext) (index : FixedKeyIndex)
    (label range : Block)
    (requested : steerPrograms key input wanted hash row index = some (label, range)) :
    range = steeredChunk row wanted hash index ^^^ label := by
  by_cases atGate : index.adaptor = CurveAdaptor.x7 ∧ index.position = 0
  · obtain ⟨adaptor, position, slot⟩ := index
    obtain ⟨rfl, rfl⟩ := atGate
    cases slot with
    | hash chunk =>
      rw [steerPrograms_hash] at requested
      cases bit : inputBits input .x7 0 with
      | true => rw [bit, if_pos rfl] at requested; exact absurd requested (by simp)
      | false =>
        rw [bit, if_neg Bool.false_ne_true] at requested
        have parts : selectedLabel key input .x7 0 = label ∧
            slotRange (.hash chunk) hash 0 (selectedLabel key input .x7 0) = range := by
          simpa using requested
        rw [← parts.2, slotRange_eq_slotChunk, parts.1]
        rfl
    | pad chunk =>
      rw [steerPrograms_pad] at requested
      cases bit : inputBits input .x7 0 with
      | false => rw [bit, if_neg Bool.false_ne_true] at requested; exact absurd requested (by simp)
      | true =>
        rw [bit, if_pos rfl] at requested
        have parts : selectedLabel key input .x7 0 = label ∧
            slotRange (.pad chunk) 0 (BitAdaptor.fieldBytes wanted ^^^ row)
              (selectedLabel key input .x7 0) = range := by simpa using requested
        rw [← parts.2, slotRange_eq_slotChunk, parts.1]
        rfl
  · rw [steerPrograms_other key input wanted hash row index atGate] at requested
    exact absurd requested (by simp)

theorem steerPrograms_label (key : InputMacKey) (input : AffineInput) (wanted : BaseField)
    (hash : BitVec 384) (row : BitAdaptor.Ciphertext) (index : FixedKeyIndex)
    (label range : Block)
    (requested : steerPrograms key input wanted hash row index = some (label, range)) :
    label = selectedLabel key input .x7 0 := by
  by_cases atGate : index.adaptor = CurveAdaptor.x7 ∧ index.position = 0
  · obtain ⟨adaptor, position, slot⟩ := index
    obtain ⟨rfl, rfl⟩ := atGate
    cases slot with
    | hash chunk =>
      rw [steerPrograms_hash] at requested
      cases bit : inputBits input .x7 0 with
      | true => rw [bit, if_pos rfl] at requested; exact absurd requested (by simp)
      | false =>
        rw [bit, if_neg Bool.false_ne_true] at requested
        have parts : selectedLabel key input .x7 0 = label ∧
            slotRange (.hash chunk) hash 0 (selectedLabel key input .x7 0) = range := by
          simpa using requested
        exact parts.1.symm
    | pad chunk =>
      rw [steerPrograms_pad] at requested
      cases bit : inputBits input .x7 0 with
      | false => rw [bit, if_neg Bool.false_ne_true] at requested; exact absurd requested (by simp)
      | true =>
        rw [bit, if_pos rfl] at requested
        have parts : selectedLabel key input .x7 0 = label ∧
            slotRange (.pad chunk) 0 (BitAdaptor.fieldBytes wanted ^^^ row)
              (selectedLabel key input .x7 0) = range := by simpa using requested
        exact parts.1.symm
  · rw [steerPrograms_other key input wanted hash row index atGate] at requested
    exact absurd requested (by simp)

/-- **The charge of the steering hop, in the concrete game terms.** The selected label is a
uniform block the first stage never reads, and the bad event of the hop names three label
values per point the first stage pinned -- summed over the indices, not multiplied by their
number. So the whole hop costs `3 q₁ / 2 ^ 128`, against the reserved
`steeringStep = 8 q / 2 ^ 128 + 6 / 2 ^ 128`. -/
theorem uniform_keyLabel_steeringBlocked_le (assigns : FamilyAssignment)
    (injective : FamilyInjective assigns) (budget : Nat)
    (small : familyPinnedCount assigns ≤ budget) (input : AffineInput)
    (outputs : GateValues BaseField) (rows : GateValues BitAdaptor.Ciphertext)
    (fibers : GateValues (BitVec 384)) (wanted : BaseField) (hash : BitVec 384) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
        {key | steeringBlocked assigns (selectedPrograms key input outputs rows fibers)
          (steerPrograms key input wanted hash (rows .x7 0))} ≤
      3 * budget / 2 ^ 128 := by
  refine le_trans (MeasureTheory.measure_mono
    (show {key : InputMacKey |
        steeringBlocked assigns (selectedPrograms key input outputs rows fibers)
          (steerPrograms key input wanted hash (rows .x7 0))} ⊆
      {key : InputMacKey | ∃ index : FixedKeyIndex,
        keyLabel key (adaptorCoordinate .x7) 0 (inputBits input .x7 0) ∈
            pinnedDomain (assigns index) ∨
          selectedChunk outputs rows fibers index ^^^
              keyLabel key (adaptorCoordinate .x7) 0 (inputBits input .x7 0) ∈
            pinnedRange (assigns index) ∨
          steeredChunk (rows .x7 0) wanted hash index ^^^
              keyLabel key (adaptorCoordinate .x7) 0 (inputBits input .x7 0) ∈
            pinnedRange (assigns index)} from fun key blocked =>
      mem_familyLabelHidden_of_blocked assigns _ _
        (keyLabel key (adaptorCoordinate .x7) 0 (inputBits input .x7 0))
        (selectedChunk outputs rows fibers) (steeredChunk (rows .x7 0) wanted hash)
        (fun index other second requested =>
          (steerPrograms_label key input wanted hash (rows .x7 0) index other second
            requested).trans (selectedLabel_eq key input .x7 0))
        (fun index first requested =>
          selectedPrograms_range key input outputs rows fibers index _ first requested)
        (fun index second requested =>
          steerPrograms_range key input wanted hash (rows .x7 0) index _ second requested)
        blocked)) ?_
  exact uniform_keyLabel_familyHidden_le assigns injective budget small
    (selectedChunk outputs rows fibers) (steeredChunk (rows .x7 0) wanted hash)
    (adaptorCoordinate .x7) 0 (inputBits input .x7 0)

/-! ### The charge fits the reserved share -/

/-- The hop's charge is inside its share of the budget, with a factor of two to spare and
the whole one-time term unused: `3 q₁ / 2 ^ 128 ≤ 8 (q₁ + q₂) / 2 ^ 128 + 6 / 2 ^ 128`. No
constant has to move. -/
theorem steeringCharge_le_steeringStep (adversary : Adversary) (parameter : Nat) :
    3 * ((adversary.firstQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 ≤
      steeringStep adversary parameter := by
  have first : (0 : ℝ) ≤ ((adversary.firstQueryBudget parameter : Nat) : ℝ) := Nat.cast_nonneg _
  have second : (0 : ℝ) ≤ ((adversary.secondQueryBudget parameter : Nat) : ℝ) :=
    Nat.cast_nonneg _
  have cast : ((adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter : Nat) : ℝ) =
      ((adversary.firstQueryBudget parameter : Nat) : ℝ) +
        ((adversary.secondQueryBudget parameter : Nat) : ℝ) := by push_cast; ring
  unfold steeringStep
  rw [cast, ← add_div]
  have key : 3 * ((adversary.firstQueryBudget parameter : Nat) : ℝ) ≤
      8 * (((adversary.firstQueryBudget parameter : Nat) : ℝ) +
        ((adversary.secondQueryBudget parameter : Nat) : ℝ)) + 6 := by linarith
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right key (by positivity)

/-! ### The key is sampled last -/

/-- The first stage of either round does not read the key: the reference table is key-free,
and the logged first stage runs on the witness tape's own key. So the key sample may be moved
past it -- which is what the charge needs, because the bad event is charged over the selected
label and the label must be sampled after the transcripts and after both fiber samples. -/
theorem steeredReferenceRound_firstStage_key [FieldCertificate] [GroupCertificate]
    (bridgeKey : BaseField) (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat)
    (auxiliary : Unit) (view : View) (key other : InputMacKey) (carrier : NonZeroBase)
    (raw : Coordinates) :
    steeredReferenceRound (fun _ => bridgeKey) scalar adversary parameter auxiliary view key
        carrier raw =
      (loggedFirstStage adversary parameter auxiliary
          (raw.table bridgeKey other, carrierBits carrier) view).bind fun outcome =>
        steeredReleasedStageTwo scalar adversary parameter auxiliary view key carrier
          (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash outcome :=
  congrArg (fun table => (loggedFirstStage adversary parameter auxiliary
      (table, carrierBits carrier) view).bind fun outcome =>
        steeredReleasedStageTwo scalar adversary parameter auxiliary view key carrier
          (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash outcome)
    (Coordinates.table_key bridgeKey raw key other)

/-- The same for the shifted round. -/
theorem shiftedReferenceRound_firstStage_key [FieldCertificate] (bridgeKey : BaseField)
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (view : View) (key other : InputMacKey) (carrier : NonZeroBase) (raw : Coordinates) :
    shiftedReferenceRound (fun _ => bridgeKey) scalar adversary parameter auxiliary view key
        carrier raw =
      (loggedFirstStage adversary parameter auxiliary
          (raw.table bridgeKey other, carrierBits carrier) view).bind fun outcome =>
        releasedStageTwo adversary parameter auxiliary view key carrier
          (raw.table bridgeKey key)
          (shiftedOutputs scalar (fun _ => bridgeKey) carrier outcome.1.1
            (encodeCoordinates outcome.1.1 raw).hash) outcome :=
  congrArg (fun table => (loggedFirstStage adversary parameter auxiliary
      (table, carrierBits carrier) view).bind fun outcome =>
        releasedStageTwo adversary parameter auxiliary view key carrier
          (raw.table bridgeKey key)
          (shiftedOutputs scalar (fun _ => bridgeKey) carrier outcome.1.1
            (encodeCoordinates outcome.1.1 raw).hash) outcome)
    (Coordinates.table_key bridgeKey raw key other)

/-- The key sample of the steered round moved past the first stage. -/
theorem bind_key_steeredReferenceRound [FieldCertificate] [GroupCertificate]
    (bridgeKey : BaseField) (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat)
    (auxiliary : Unit) (view : View) (carrier : NonZeroBase) (raw : Coordinates) :
    ((PMF.uniformOfFintype InputMacKey).bind fun key =>
        steeredReferenceRound (fun _ => bridgeKey) scalar adversary parameter auxiliary view key
          carrier raw) =
      (loggedFirstStage adversary parameter auxiliary
          (raw.table bridgeKey witnessTape.inputMacKey, carrierBits carrier) view).bind
        fun outcome =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            steeredReleasedStageTwo scalar adversary parameter auxiliary view key carrier
              (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash outcome := by
  rw [congrArg (PMF.bind (PMF.uniformOfFintype InputMacKey)) (funext fun key =>
    steeredReferenceRound_firstStage_key bridgeKey scalar adversary parameter auxiliary view key
      witnessTape.inputMacKey carrier raw)]
  exact PMF.bind_comm _ _ _

/-- The key sample of the shifted round moved past the first stage. -/
theorem bind_key_shiftedReferenceRound [FieldCertificate] (bridgeKey : BaseField)
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (view : View) (carrier : NonZeroBase) (raw : Coordinates) :
    ((PMF.uniformOfFintype InputMacKey).bind fun key =>
        shiftedReferenceRound (fun _ => bridgeKey) scalar adversary parameter auxiliary view key
          carrier raw) =
      (loggedFirstStage adversary parameter auxiliary
          (raw.table bridgeKey witnessTape.inputMacKey, carrierBits carrier) view).bind
        fun outcome =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            releasedStageTwo adversary parameter auxiliary view key carrier
              (raw.table bridgeKey key)
              (shiftedOutputs scalar (fun _ => bridgeKey) carrier outcome.1.1
                (encodeCoordinates outcome.1.1 raw).hash) outcome := by
  rw [congrArg (PMF.bind (PMF.uniformOfFintype InputMacKey)) (funext fun key =>
    shiftedReferenceRound_firstStage_key bridgeKey scalar adversary parameter auxiliary view key
      witnessTape.inputMacKey carrier raw)]
  exact PMF.bind_comm _ _ _

/-! ### The first stage in the lazy family model -/

/-- A logged first stage consumed as a run. -/
theorem bind_loggedFirstStage {Value : Type} (adversary : Adversary) (parameter : Nat)
    (auxiliary : Unit) (circuit : Garbling.Public) (view : View)
    (continuation : (AffineInput × adversary.State) × List Query → PMF Value) :
    (loggedFirstStage adversary parameter auxiliary circuit view).bind continuation =
      ((adversary.chooseInput parameter circuit auxiliary).run idealOracle
          (firstState view circuit.1 ⟨1, one_ne_zero⟩ witnessTape.inputMacKey)).bind
        fun output => continuation (output.1, output.2.log) :=
  bind_of_map _ _ _

/-- The state the first stage starts from, with the permutation family left blank. The lazy
family run never reads it, and the eager run reads it only through `setFamily`. -/
def chargeFirstState
    (rest : PermutationOracle Garbling.EncIndex Block × (BN254.BaseField → Block × Block))
    (table : CurveMembership.Table) : State :=
  firstState (⟨fun _ => Equiv.refl Block⟩, rest) table ⟨1, one_ne_zero⟩ witnessTape.inputMacKey

theorem setFamily_chargeFirstState
    (rest : PermutationOracle Garbling.EncIndex Block × (BN254.BaseField → Block × Block))
    (table : CurveMembership.Table) (oracle : PermutationOracle FixedKeyIndex Block) :
    setFamily (chargeFirstState rest table) oracle =
      firstState (oracle, rest) table ⟨1, one_ne_zero⟩ witnessTape.inputMacKey := rfl

/-- The steered round with the permutation family conditioned on the first stage's
transcripts and the key sampled afterwards. This is the sample order the charge needs. -/
theorem lazy_steeredReferenceRound [FieldCertificate] [GroupCertificate] (bridgeKey : BaseField)
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (rest : PermutationOracle Garbling.EncIndex Block × (BN254.BaseField → Block × Block))
    (carrier : NonZeroBase) (raw : Coordinates) :
    ((PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype InputMacKey).bind fun key =>
          steeredReferenceRound (fun _ => bridgeKey) scalar adversary parameter auxiliary
            (oracle, rest) key carrier raw) =
      (lazyFamilyRun (adversary.chooseInput parameter
            (raw.table bridgeKey witnessTape.inputMacKey, carrierBits carrier) auxiliary)
          (chargeFirstState rest (raw.table bridgeKey witnessTape.inputMacKey))
          (fun _ _ => none)).bind fun output =>
        (familyLaw output.2).bind fun oracle =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            steeredReleasedStageTwo scalar adversary parameter auxiliary (oracle, rest) key
              carrier (raw.table bridgeKey key) (encodeCoordinates output.1.1.1 raw).hash
              output.1 := by
  have left : ((PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype InputMacKey).bind fun key =>
          steeredReferenceRound (fun _ => bridgeKey) scalar adversary parameter auxiliary
            (oracle, rest) key carrier raw) =
      (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        ((adversary.chooseInput parameter
            (raw.table bridgeKey witnessTape.inputMacKey, carrierBits carrier) auxiliary).run
            idealOracle
            (setFamily (chargeFirstState rest (raw.table bridgeKey witnessTape.inputMacKey))
              oracle)).bind fun output =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            steeredReleasedStageTwo scalar adversary parameter auxiliary (oracle, rest) key
              carrier (raw.table bridgeKey key)
              (encodeCoordinates (output.1, output.2.log).1.1 raw).hash
              (output.1, output.2.log) := by
    refine congrArg (PMF.bind _) (funext fun oracle => ?_)
    rw [bind_key_steeredReferenceRound bridgeKey scalar adversary parameter auxiliary
      (oracle, rest) carrier raw, bind_loggedFirstStage]
    rfl
  rw [left]
  exact uniform_run_familyLaw
    (adversary.chooseInput parameter
      (raw.table bridgeKey witnessTape.inputMacKey, carrierBits carrier) auxiliary)
    (chargeFirstState rest (raw.table bridgeKey witnessTape.inputMacKey))
    (fun outcome oracle => (PMF.uniformOfFintype InputMacKey).bind fun key =>
      steeredReleasedStageTwo scalar adversary parameter auxiliary (oracle, rest) key carrier
        (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash outcome)

/-- The shifted round in the same sample order. -/
theorem lazy_shiftedReferenceRound [FieldCertificate] (bridgeKey : BaseField)
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (rest : PermutationOracle Garbling.EncIndex Block × (BN254.BaseField → Block × Block))
    (carrier : NonZeroBase) (raw : Coordinates) :
    ((PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype InputMacKey).bind fun key =>
          shiftedReferenceRound (fun _ => bridgeKey) scalar adversary parameter auxiliary
            (oracle, rest) key carrier raw) =
      (lazyFamilyRun (adversary.chooseInput parameter
            (raw.table bridgeKey witnessTape.inputMacKey, carrierBits carrier) auxiliary)
          (chargeFirstState rest (raw.table bridgeKey witnessTape.inputMacKey))
          (fun _ _ => none)).bind fun output =>
        (familyLaw output.2).bind fun oracle =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            releasedStageTwo adversary parameter auxiliary (oracle, rest) key carrier
              (raw.table bridgeKey key)
              (shiftedOutputs scalar (fun _ => bridgeKey) carrier output.1.1.1
                (encodeCoordinates output.1.1.1 raw).hash) output.1 := by
  have left : ((PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype InputMacKey).bind fun key =>
          shiftedReferenceRound (fun _ => bridgeKey) scalar adversary parameter auxiliary
            (oracle, rest) key carrier raw) =
      (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        ((adversary.chooseInput parameter
            (raw.table bridgeKey witnessTape.inputMacKey, carrierBits carrier) auxiliary).run
            idealOracle
            (setFamily (chargeFirstState rest (raw.table bridgeKey witnessTape.inputMacKey))
              oracle)).bind fun output =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            releasedStageTwo adversary parameter auxiliary (oracle, rest) key carrier
              (raw.table bridgeKey key)
              (shiftedOutputs scalar (fun _ => bridgeKey) carrier (output.1, output.2.log).1.1
                (encodeCoordinates (output.1, output.2.log).1.1 raw).hash)
              (output.1, output.2.log) := by
    refine congrArg (PMF.bind _) (funext fun oracle => ?_)
    rw [bind_key_shiftedReferenceRound bridgeKey scalar adversary parameter auxiliary
      (oracle, rest) carrier raw, bind_loggedFirstStage]
    rfl
  rw [left]
  exact uniform_run_familyLaw
    (adversary.chooseInput parameter
      (raw.table bridgeKey witnessTape.inputMacKey, carrierBits carrier) auxiliary)
    (chargeFirstState rest (raw.table bridgeKey witnessTape.inputMacKey))
    (fun outcome oracle => (PMF.uniformOfFintype InputMacKey).bind fun key =>
      releasedStageTwo adversary parameter auxiliary (oracle, rest) key carrier
        (raw.table bridgeKey key)
        (shiftedOutputs scalar (fun _ => bridgeKey) carrier outcome.1.1
          (encodeCoordinates outcome.1.1 raw).hash) outcome)

/-! ### Averaging a pointwise advantage bound over an infinite sample -/

/-- A uniform pointwise advantage bound survives an outer sample, with **no** finiteness
assumption on the sample type, and with the bound required only on the sample's support.

`advantage_bind_le_of_le` is stated with `[Fintype Sample]`, which the lazy family run's
output type does not have -- it carries a `List Query` and the adversary's state. The charge
has to average its per-transcript bound over exactly that type, so it needs this form. The
support restriction is what lets the per-transcript bound use the run's own transcript
invariants, which hold only on the support. The proof avoids real summability altogether:
the pointwise bound is turned into the two `ENNReal` inequalities
`p true ≤ q true + ofReal bound`, which survive an unconditional `ENNReal` tsum. -/
theorem advantage_bind_le_pointwise {Sample : Type} (law : PMF Sample)
    (first second : Sample → PMF Bool) (bound : ℝ)
    (pointwise : ∀ sample ∈ law.support, advantage (first sample) (second sample) ≤ bound) :
    advantage (law.bind first) (law.bind second) ≤ bound := by
  obtain ⟨witness, witnessMember⟩ := law.support_nonempty
  have nonneg : 0 ≤ bound := by
    have step := pointwise witness witnessMember
    unfold advantage at step
    exact le_trans (abs_nonneg _) step
  have pointwiseShift : ∀ (left right : Sample → PMF Bool),
      (∀ sample ∈ law.support, advantage (left sample) (right sample) ≤ bound) →
      ∀ sample ∈ law.support,
        (left sample) true ≤ (right sample) true + ENNReal.ofReal bound := by
    intro left right step sample member
    have base := step sample member
    unfold advantage at base
    have le : ((left sample) true).toReal ≤ ((right sample) true).toReal + bound := by
      have half := (abs_sub_le_iff.mp base).1
      linarith
    have rewrite : (right sample) true + ENNReal.ofReal bound =
        ENNReal.ofReal (((right sample) true).toReal + bound) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg nonneg,
        ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
    rw [rewrite]
    exact (ENNReal.le_ofReal_iff_toReal_le (PMF.apply_ne_top _ _)
      (add_nonneg ENNReal.toReal_nonneg nonneg)).mpr le
  have shift : ∀ (left right : Sample → PMF Bool),
      (∀ sample ∈ law.support, (left sample) true ≤ (right sample) true + ENNReal.ofReal bound) →
      (law.bind left) true ≤ (law.bind right) true + ENNReal.ofReal bound := by
    intro left right step
    rw [PMF.bind_apply, PMF.bind_apply]
    calc ∑' sample, law sample * (left sample) true
        ≤ ∑' sample, law sample * ((right sample) true + ENNReal.ofReal bound) := by
          refine ENNReal.tsum_le_tsum fun sample => ?_
          by_cases member : sample ∈ law.support
          · exact mul_le_mul_of_nonneg_left (step sample member) zero_le
          · rw [(PMF.apply_eq_zero_iff law sample).mpr member, zero_mul, zero_mul]
      _ = ∑' sample, (law sample * (right sample) true +
            law sample * ENNReal.ofReal bound) := tsum_congr fun sample => mul_add _ _ _
      _ = (∑' sample, law sample * (right sample) true) +
            ∑' sample, law sample * ENNReal.ofReal bound := ENNReal.tsum_add
      _ = (∑' sample, law sample * (right sample) true) + ENNReal.ofReal bound := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have convert : ∀ (left right : Sample → PMF Bool),
      (law.bind left) true ≤ (law.bind right) true + ENNReal.ofReal bound →
      ((law.bind left) true).toReal - ((law.bind right) true).toReal ≤ bound := by
    intro left right step
    have finite : (law.bind right) true + ENNReal.ofReal bound ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, ENNReal.ofReal_ne_top⟩
    have mono := ENNReal.toReal_mono finite step
    rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal nonneg] at mono
    linarith
  have backward : ∀ sample ∈ law.support, advantage (second sample) (first sample) ≤ bound := by
    intro sample member
    have step := pointwise sample member
    unfold advantage at step ⊢
    rwa [abs_sub_comm]
  unfold advantage
  exact abs_sub_le_iff.mpr
    ⟨convert first second (shift first second (pointwiseShift first second pointwise)),
      convert second first (shift second first (pointwiseShift second first backward))⟩

/-! ### Four independent samples in the order the charge needs -/

/-- Four independent samples may be drawn in the order `third, fourth, second, first`.

This is the sample order of the hop: the two fiber samples first, then the selected label
(over which the bad event is priced), and only then the conditioned permutation family. -/
theorem bind_comm_outward {First Second Third Fourth Result : Type} (first : PMF First)
    (second : PMF Second) (third : PMF Third) (fourth : PMF Fourth)
    (body : First → Second → Third → Fourth → PMF Result) :
    (first.bind fun one => second.bind fun two => third.bind fun three =>
        fourth.bind fun four => body one two three four) =
      third.bind fun three => fourth.bind fun four => second.bind fun two =>
        first.bind fun one => body one two three four := by
  have inward : (first.bind fun one => second.bind fun two => third.bind fun three =>
        fourth.bind fun four => body one two three four) =
      second.bind fun two => third.bind fun three => fourth.bind fun four =>
        first.bind fun one => body one two three four := by
    refine (PMF.bind_comm first second _).trans ?_
    refine congrArg (PMF.bind second) (funext fun two => ?_)
    refine (PMF.bind_comm first third _).trans ?_
    exact congrArg (PMF.bind third) (funext fun _ => PMF.bind_comm first fourth _)
  refine inward.trans ?_
  refine (PMF.bind_comm second third _).trans ?_
  exact congrArg (PMF.bind third) (funext fun _ => PMF.bind_comm second fourth _)

/-- An identical-until-bad hop of four samples whose bad event lives on the middle one and
the two outer ones, and whose two laws agree -- for every good value of those three -- after
the innermost sample is integrated out.

This is the shape of the steering hop: the permutation family is the innermost sample, the
selected label is the one the bad event is priced over, and the two fiber samples are the
ones the bound is uniform in. -/
theorem advantage_bind_le_badMiddle {Inner Label First Second : Type} (inner : PMF Inner)
    (label : PMF Label) (first : PMF First) (second : PMF Second)
    (leftBody rightBody : Inner → Label → First → Second → PMF Bool)
    (bad : Label → First → Second → Prop) (bound : ℝ)
    (agree : ∀ (choice : Label) (one : First) (two : Second), ¬ bad choice one two →
      (inner.bind fun value => leftBody value choice one two) =
        inner.bind fun value => rightBody value choice one two)
    (mass : ∀ (one : First) (two : Second),
      (label.toOuterMeasure {choice | bad choice one two}).toReal ≤ bound) :
    advantage
        (inner.bind fun value => label.bind fun choice => first.bind fun one =>
          second.bind fun two => leftBody value choice one two)
        (inner.bind fun value => label.bind fun choice => first.bind fun one =>
          second.bind fun two => rightBody value choice one two) ≤ bound := by
  rw [bind_comm_outward inner label first second leftBody,
    bind_comm_outward inner label first second rightBody]
  refine advantage_bind_le_pointwise first _ _ bound fun one _ => ?_
  refine advantage_bind_le_pointwise second _ _ bound fun two _ => ?_
  exact le_trans (advantage_bind_le_bad label label _ _ {choice | bad choice one two}
    (fun _ _ => rfl) fun choice good => agree choice one two good) (mass one two)

/-- Three blocks of a query budget over `2 ^ 128`, as a real number. -/
theorem toReal_three_budget (budget : Nat) :
    ((3 : ENNReal) * (budget : ENNReal) / 2 ^ 128).toReal = 3 * (budget : ℝ) / 2 ^ 128 := by
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat]

/-! ### The hop, per first-stage transcript -/

/-- **The steering hop, at one lazy first-stage transcript.** Given transcripts that are
injective, cover their own log, and pin at most `budget` points in total, the shifted second
stage and the steered second stage are within `3 * budget / 2 ^ 128`.

Off the curve the two laws are equal and the bound is free. On the curve the key is sampled
last, so both fiber samples move outside it, and for every pair of fiber samples the two
laws agree unless the selected label is one of the `3 * budget` values the transcripts
block. The table is key-free, so the bad event's rows are, which is what makes its mass
uniform in the key. -/
theorem advantage_bind_familyLaw_shifted_steered_le [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (rest : PermutationOracle Garbling.EncIndex Block × (BN254.BaseField → Block × Block))
    (carrier : NonZeroBase) (bridgeKey : BaseField) (raw : Coordinates)
    (outcome : (AffineInput × adversary.State) × List Query) (assigns : FamilyAssignment)
    (injective : FamilyInjective assigns) (covers : FamilyCovers assigns outcome.2)
    (budget : Nat) (small : familyPinnedCount assigns ≤ budget) :
    advantage
        ((familyLaw assigns).bind fun oracle =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            releasedStageTwo adversary parameter auxiliary (oracle, rest) key carrier
              (raw.table bridgeKey key)
              (shiftedOutputs scalar (fun _ => bridgeKey) carrier outcome.1.1
                (encodeCoordinates outcome.1.1 raw).hash) outcome)
        ((familyLaw assigns).bind fun oracle =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            steeredReleasedStageTwo scalar adversary parameter auxiliary (oracle, rest) key
              carrier (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash
              outcome) ≤
      3 * (budget : ℝ) / 2 ^ 128 := by
  have nonneg : (0 : ℝ) ≤ 3 * (budget : ℝ) / 2 ^ 128 := by positivity
  have tableEq : ∀ key : InputMacKey,
      raw.table bridgeKey key = raw.table bridgeKey witnessTape.inputMacKey :=
    fun key => Coordinates.table_key bridgeKey raw key witnessTape.inputMacKey
  by_cases onCurve : curveGap outcome.1.1 = 0
  · have shifted : shiftedOutputs scalar (fun _ => bridgeKey) carrier outcome.1.1
        (encodeCoordinates outcome.1.1 raw).hash =
        shiftSteering (hybridBridge scalar carrier - bridgeKey)
          (encodeCoordinates outcome.1.1 raw).hash := by
      rw [shiftedOutputs, if_pos onCurve]
    rw [shifted]
    have steeredPointwise : ∀ (oracle : PermutationOracle FixedKeyIndex Block)
        (key : InputMacKey),
        steeredReleasedStageTwo scalar adversary parameter auxiliary (oracle, rest) key carrier
            (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash outcome =
          (uniformHashFibers (encodeCoordinates outcome.1.1 raw).hash).bind fun fibers =>
            (uniformHashFiber ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                (hybridBridge scalar carrier - bridgeKey))).bind fun hash =>
              (hybridStageTwo adversary parameter auxiliary
                  (raw.table bridgeKey witnessTape.inputMacKey, carrierBits carrier)
                  outcome.1.1 outcome.1.2
                  (programAll (stageTwoState (programIndices (selectedPrograms key outcome.1.1
                      (encodeCoordinates outcome.1.1 raw).hash
                      (tableRow (raw.table bridgeKey witnessTape.inputMacKey)) fibers) oracle,
                      rest) outcome.2 (raw.table bridgeKey witnessTape.inputMacKey) carrier key)
                    (steerRequests (raw.table bridgeKey witnessTape.inputMacKey)
                      (selectedLabel key outcome.1.1 .x7 0) outcome.1.1
                      ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                        (hybridBridge scalar carrier - bridgeKey)) hash))).map Prod.fst := by
      intro oracle key
      rw [steeredReleasedStageTwo_programAll scalar adversary parameter auxiliary (oracle, rest)
        key carrier bridgeKey raw outcome onCurve, tableEq key]
    have shiftedPointwise : ∀ (oracle : PermutationOracle FixedKeyIndex Block)
        (key : InputMacKey),
        releasedStageTwo adversary parameter auxiliary (oracle, rest) key carrier
            (raw.table bridgeKey key)
            (shiftSteering (hybridBridge scalar carrier - bridgeKey)
              (encodeCoordinates outcome.1.1 raw).hash) outcome =
          (uniformHashFibers (encodeCoordinates outcome.1.1 raw).hash).bind fun fibers =>
            (uniformHashFiber ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                (hybridBridge scalar carrier - bridgeKey))).bind fun hash =>
              (hybridStageTwo adversary parameter auxiliary
                  (raw.table bridgeKey witnessTape.inputMacKey, carrierBits carrier)
                  outcome.1.1 outcome.1.2
                  (stageTwoState (shiftedOracle key outcome.1.1
                      (encodeCoordinates outcome.1.1 raw).hash
                      (tableRow (raw.table bridgeKey witnessTape.inputMacKey)) fibers
                      ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
                        (hybridBridge scalar carrier - bridgeKey)) hash oracle, rest)
                    outcome.2 (raw.table bridgeKey witnessTape.inputMacKey) carrier key)).map
                Prod.fst := by
      intro oracle key
      rw [releasedStageTwo_shifted adversary parameter auxiliary (oracle, rest) key carrier
        (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash
        (hybridBridge scalar carrier - bridgeKey) outcome, tableEq key]
    rw [congrArg (PMF.bind (familyLaw assigns)) (funext fun oracle =>
        congrArg (PMF.bind (PMF.uniformOfFintype InputMacKey)) (funext fun key =>
          shiftedPointwise oracle key)),
      congrArg (PMF.bind (familyLaw assigns)) (funext fun oracle =>
        congrArg (PMF.bind (PMF.uniformOfFintype InputMacKey)) (funext fun key =>
          steeredPointwise oracle key))]
    refine advantage_bind_le_badMiddle (familyLaw assigns) (PMF.uniformOfFintype InputMacKey)
      (uniformHashFibers (encodeCoordinates outcome.1.1 raw).hash)
      (uniformHashFiber ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
        (hybridBridge scalar carrier - bridgeKey))) _ _
      (fun key fibers hash => steeringBlocked assigns
        (selectedPrograms key outcome.1.1 (encodeCoordinates outcome.1.1 raw).hash
          (tableRow (raw.table bridgeKey witnessTape.inputMacKey)) fibers)
        (steerPrograms key outcome.1.1 ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
            (hybridBridge scalar carrier - bridgeKey)) hash
          (tableRow (raw.table bridgeKey witnessTape.inputMacKey) .x7 0))) _ ?_ ?_
    · intro key fibers hash good
      exact (bind_familyLaw_programAll_eq_shifted adversary parameter auxiliary rest key carrier
        (raw.table bridgeKey witnessTape.inputMacKey) outcome.1.1 outcome.1.2 outcome.2
        (encodeCoordinates outcome.1.1 raw).hash fibers
        ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
          (hybridBridge scalar carrier - bridgeKey)) hash assigns injective covers good).symm
    · intro fibers hash
      refine le_trans (ENNReal.toReal_mono (by finiteness)
        (uniform_keyLabel_steeringBlocked_le assigns injective budget small outcome.1.1
          (encodeCoordinates outcome.1.1 raw).hash
          (tableRow (raw.table bridgeKey witnessTape.inputMacKey)) fibers
          ((encodeCoordinates outcome.1.1 raw).hash .x7 0 +
            (hybridBridge scalar carrier - bridgeKey)) hash)) ?_
      exact le_of_eq (toReal_three_budget budget)
  · have shifted : shiftedOutputs scalar (fun _ => bridgeKey) carrier outcome.1.1
        (encodeCoordinates outcome.1.1 raw).hash =
        (encodeCoordinates outcome.1.1 raw).hash := by
      rw [shiftedOutputs, if_neg onCurve]
    have same : ((familyLaw assigns).bind fun oracle =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            steeredReleasedStageTwo scalar adversary parameter auxiliary (oracle, rest) key
              carrier (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash
              outcome) =
        (familyLaw assigns).bind fun oracle =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            releasedStageTwo adversary parameter auxiliary (oracle, rest) key carrier
              (raw.table bridgeKey key)
              (shiftedOutputs scalar (fun _ => bridgeKey) carrier outcome.1.1
                (encodeCoordinates outcome.1.1 raw).hash) outcome := by
      rw [shifted]
      exact congrArg (PMF.bind _) (funext fun oracle =>
        congrArg (PMF.bind _) (funext fun key =>
          steeredReleasedStageTwo_offCurve scalar adversary parameter auxiliary (oracle, rest)
            key carrier (raw.table bridgeKey key) (encodeCoordinates outcome.1.1 raw).hash
            outcome onCurve))
    rw [same, advantage_eq, sub_self, abs_zero]
    exact nonneg

end

end Kriterion.ArgoMAC.Security
