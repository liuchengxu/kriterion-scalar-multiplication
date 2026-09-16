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

end

end Kriterion.ArgoMAC.Security
