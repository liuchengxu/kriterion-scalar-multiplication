/-
This file finishes the simulated side's walk to the reference game, up to the
steering. The two oracle hops of the simulated side left it in the reference
game's shape but still carrying the secrets of its own reparametrisation: a
nonzero curve mask, and one fresh 384-bit digest per gate standing both for the
table's hash secret and for the reference game's fiber sample. The simulated
side has to pay for the same two replacements as the hybrid side -- the chain
reaches the simulated game only through a reference game, so the two sides
cannot share them.

Both replacements and the deferral of the fiber sample are the hybrid side's,
verbatim: the mask costs `2 / p`, the digests `1270 * p / 2 ^ 384`, and the move
of the fiber sample to the selected outputs is free because the second stage
reads the fibers only through `programSelected`. The steering does not change
any of this -- it reads the state the programming produced, and the marginal
lemma is stated for an arbitrary second stage on that state.

What comes out is `R(u)` plus the steering: the reference game of the tape's own
bridge key `u`, whose second stage hands over the honest labels and then steers.
Identifying that with the reference game of `carrier / scalar` is step 7 and is
not done here.
-/

import Proof.SimulatedChain

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

noncomputable section

/-! ### The two bodies of the simulated side's step 2 -/

/-- The reference-shaped round with the steering, and with the fiber family fixed before
the first stage: this is what the simulated side's two oracle hops left. -/
def steeredDigestedBody [FieldCertificate] [GroupCertificate] (bridge : NonZeroBase → BaseField)
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (datum : ReferenceDatum) (mask : BaseField) (hash : GateValues BaseField)
    (fibers : GateValues (BitVec 384)) : PMF Bool :=
  (loggedFirstStage adversary parameter auxiliary (referenceCircuit bridge datum mask hash)
      (referenceView datum)).bind fun outcome =>
    (selectedSimulatedStageTwo adversary parameter auxiliary
      (referenceCircuit bridge datum mask hash) outcome.1.1
      (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2
      (encodeCoordinates outcome.1.1 (referenceRaw datum mask hash)).hash fibers
      (stageTwoState (referenceView datum) outcome.2
        (referenceCircuit bridge datum mask hash).1 (referenceCarrier datum)
        (referenceKey datum))).map Prod.fst

/-- The reference-shaped round with the steering and with the fiber family sampled after the
input is chosen, at the selected outputs: this is `R(bridge)` plus the steering. -/
def steeredFiberedBody [FieldCertificate] [GroupCertificate] (bridge : NonZeroBase → BaseField)
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (datum : ReferenceDatum) (mask : BaseField) (hash : GateValues BaseField) : PMF Bool :=
  (loggedFirstStage adversary parameter auxiliary (referenceCircuit bridge datum mask hash)
      (referenceView datum)).bind fun outcome =>
    (uniformHashFibers
        (encodeCoordinates outcome.1.1 (referenceRaw datum mask hash)).hash).bind fun fibers =>
      (selectedSimulatedStageTwo adversary parameter auxiliary
        (referenceCircuit bridge datum mask hash) outcome.1.1
        (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2
        (encodeCoordinates outcome.1.1 (referenceRaw datum mask hash)).hash fibers
        (stageTwoState (referenceView datum) outcome.2
          (referenceCircuit bridge datum mask hash).1 (referenceCarrier datum)
          (referenceKey datum))).map Prod.fst

/-! ### The simulated side in the shape of step 2 -/

/-- The key-free sample of the simulated side is a uniform sample of its product type. -/
theorem simulatedData_eq_uniform : simulatedData = PMF.uniformOfFintype SimulatedDatum := by
  have pureForm : simulatedData =
      (PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
          (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
            (PMF.uniformOfFintype (GateValues (BitVec 384) ×
                GateValues BitAdaptor.Ciphertext)).bind fun secrets =>
              (PMF.uniformOfFintype (NonZeroBase × BaseField × BaseField)).bind fun curve =>
                (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
                  PMF.pure ((bridgeKey, tape, oracle, secrets, curve, carrier) :
                    SimulatedDatum) := by
    conv_lhs => rw [← PMF.bind_pure simulatedData]
    exact simulatedData_bind PMF.pure
  rw [pureForm]
  simp only [uniformOfFintype_bind_prod]
  exact PMF.bind_pure _

/-- The simulated side's public value is the reference-shaped one at the constant bridge key
`u`: the reference table ignores the label key, so the key the second stage uses may be read
off the sample. -/
theorem simulatedCircuit_eq_referenceCircuit (key : InputMacKey) (datum : SimulatedDatum) :
    simulatedCircuit datum =
      referenceCircuit (fun _ => simulatedBridgeKey datum) (referenceOf key datum.2)
        (hybridMask datum.2) (digestField (hybridDigests datum.2)) :=
  congrArg (fun table => (table, carrierBits (hybridCarrier datum.2)))
    (Coordinates.table_key _ _ _ _)

/-- The game the simulated side's two oracle hops left, with the mask and the digests
floated out. -/
def steeredDigestedGame [FieldCertificate] [GroupCertificate] (bridge : NonZeroBase → BaseField)
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    PMF Bool :=
  (PMF.uniformOfFintype ReferenceDatum).bind fun datum =>
    ((PMF.uniformOfFintype NonZeroBase).map NonZeroBase.value).bind fun mask =>
      (PMF.uniformOfFintype (GateValues (BitVec 384))).bind fun digests =>
        steeredDigestedBody bridge scalar adversary parameter auxiliary datum mask
          (digestField digests) digests

/-- Floating the bridge key, the mask and the digests out of the simulated side's sample. -/
def steeredSampleEquiv :
    InputMacKey × SimulatedDatum ≃
      NonZeroBase × ReferenceDatum × NonZeroBase × GateValues (BitVec 384) where
  toFun sample :=
    (sample.2.1, referenceOf sample.1 sample.2.2, sample.2.2.2.2.2.1.1,
      hybridDigests sample.2.2)
  invFun sample :=
    (sample.2.1.1, sample.1,
      (sample.2.1.2.1, sample.2.1.2.2.1, (sample.2.2.2, referencePads sample.2.1),
        (sample.2.2.1, referenceR1 sample.2.1, referenceR2 sample.2.1),
        referenceCarrier sample.2.1))
  left_inv := by
    rintro ⟨key, bridgeKey, tape, oracle, ⟨digests, pads⟩, ⟨mask, r1, r2⟩, carrier⟩
    rfl
  right_inv := by
    rintro ⟨bridgeKey, ⟨key, tape, oracle, pads, ⟨r1, r2⟩, carrier⟩, mask, digests⟩
    rfl

/-- The simulated side after both oracle hops, with the bridge key, the mask and the digests
floated out of the sample so that step 2 can replace them. -/
theorem steeredDigested_eq [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    steeredDigested scalar adversary parameter auxiliary =
      (PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        steeredDigestedGame (fun _ => bridgeKey.value) scalar adversary parameter auxiliary := by
  have body : ∀ (key : InputMacKey) (datum : SimulatedDatum),
      ((loggedFirstStage adversary parameter auxiliary (simulatedCircuit datum)
          (hybridView datum.2)).bind fun outcome =>
        (selectedSimulatedStageTwo adversary parameter auxiliary (simulatedCircuit datum)
          outcome.1.1 (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2
          (encodeCoordinates outcome.1.1 (hybridRaw datum.2)).hash (hybridDigests datum.2)
          (stageTwoState (hybridView datum.2) outcome.2 (simulatedCircuit datum).1
            (hybridCarrier datum.2) key)).map Prod.fst) =
        steeredDigestedBody (fun _ => simulatedBridgeKey datum) scalar adversary parameter
          auxiliary (referenceOf key datum.2) (hybridMask datum.2)
          (digestField (hybridDigests datum.2)) (hybridDigests datum.2) := by
    intro key datum
    rw [simulatedCircuit_eq_referenceCircuit key datum]
    rfl
  have left : steeredDigested scalar adversary parameter auxiliary =
      (PMF.uniformOfFintype (InputMacKey × SimulatedDatum)).bind fun sample =>
        steeredDigestedBody (fun _ => simulatedBridgeKey sample.2) scalar adversary parameter
          auxiliary (referenceOf sample.1 sample.2.2) (hybridMask sample.2.2)
          (digestField (hybridDigests sample.2.2)) (hybridDigests sample.2.2) := by
    unfold steeredDigested
    rw [simulatedData_eq_uniform]
    rw [show ((PMF.uniformOfFintype InputMacKey).bind fun key =>
        (PMF.uniformOfFintype SimulatedDatum).bind fun datum =>
          (loggedFirstStage adversary parameter auxiliary (simulatedCircuit datum)
              (hybridView datum.2)).bind fun outcome =>
            (selectedSimulatedStageTwo adversary parameter auxiliary (simulatedCircuit datum)
              outcome.1.1 (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2
              (encodeCoordinates outcome.1.1 (hybridRaw datum.2)).hash (hybridDigests datum.2)
              (stageTwoState (hybridView datum.2) outcome.2 (simulatedCircuit datum).1
                (hybridCarrier datum.2) key)).map Prod.fst) =
        ((PMF.uniformOfFintype InputMacKey).bind fun key =>
          (PMF.uniformOfFintype SimulatedDatum).bind fun datum =>
            steeredDigestedBody (fun _ => simulatedBridgeKey datum) scalar adversary parameter
              auxiliary (referenceOf key datum.2) (hybridMask datum.2)
              (digestField (hybridDigests datum.2)) (hybridDigests datum.2)) from
      congrArg (PMF.bind _) (funext fun key =>
        congrArg (PMF.bind _) (funext fun datum => body key datum))]
    exact uniformOfFintype_bind_prod fun key datum =>
      steeredDigestedBody (fun _ => simulatedBridgeKey datum) scalar adversary parameter
        auxiliary (referenceOf key datum.2) (hybridMask datum.2)
        (digestField (hybridDigests datum.2)) (hybridDigests datum.2)
  have right : ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        steeredDigestedGame (fun _ => bridgeKey.value) scalar adversary parameter auxiliary) =
      (PMF.uniformOfFintype (NonZeroBase × ReferenceDatum × NonZeroBase ×
        GateValues (BitVec 384))).bind fun sample =>
          steeredDigestedBody (fun _ => sample.1.value) scalar adversary parameter auxiliary
            sample.2.1 sample.2.2.1.value (digestField sample.2.2.2) sample.2.2.2 := by
    unfold steeredDigestedGame
    have masked : ∀ (bridgeKey : NonZeroBase) (datum : ReferenceDatum),
        (((PMF.uniformOfFintype NonZeroBase).map NonZeroBase.value).bind fun mask =>
            (PMF.uniformOfFintype (GateValues (BitVec 384))).bind fun digests =>
              steeredDigestedBody (fun _ => bridgeKey.value) scalar adversary parameter auxiliary
                datum mask (digestField digests) digests) =
          (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
            (PMF.uniformOfFintype (GateValues (BitVec 384))).bind fun digests =>
              steeredDigestedBody (fun _ => bridgeKey.value) scalar adversary parameter auxiliary
                datum mask.value (digestField digests) digests := by
      intro bridgeKey datum
      rw [PMF.bind_map]
      rfl
    rw [congrArg (PMF.bind _) (funext fun bridgeKey =>
      congrArg (PMF.bind _) (funext (masked bridgeKey)))]
    rw [congrArg (PMF.bind (PMF.uniformOfFintype NonZeroBase)) (funext fun bridgeKey =>
      congrArg (PMF.bind (PMF.uniformOfFintype ReferenceDatum)) (funext fun datum =>
        uniformOfFintype_bind_prod fun (mask : NonZeroBase) (digests : GateValues (BitVec 384)) =>
          steeredDigestedBody (fun _ => bridgeKey.value) scalar adversary parameter auxiliary
            datum mask.value (digestField digests) digests))]
    rw [congrArg (PMF.bind (PMF.uniformOfFintype NonZeroBase)) (funext fun bridgeKey =>
      uniformOfFintype_bind_prod fun (datum : ReferenceDatum)
        (pair : NonZeroBase × GateValues (BitVec 384)) =>
          steeredDigestedBody (fun _ => bridgeKey.value) scalar adversary parameter auxiliary
            datum pair.1.value (digestField pair.2) pair.2)]
    exact uniformOfFintype_bind_prod fun (bridgeKey : NonZeroBase)
      (pair : ReferenceDatum × NonZeroBase × GateValues (BitVec 384)) =>
        steeredDigestedBody (fun _ => bridgeKey.value) scalar adversary parameter auxiliary
          pair.1 pair.2.1.value (digestField pair.2.2) pair.2.2
  rw [left, right, ← uniformOfFintype_bind_bijection steeredSampleEquiv]
  rfl

/-! ### Step 2 of the simulated side, hop by hop -/

/-- The simulated side's game with the curve mask uniform over the whole field. -/
def steeredMaskedGame [FieldCertificate] [GroupCertificate] (bridge : NonZeroBase → BaseField)
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    PMF Bool :=
  (PMF.uniformOfFintype ReferenceDatum).bind fun datum =>
    (PMF.uniformOfFintype BaseField).bind fun mask =>
      (PMF.uniformOfFintype (GateValues (BitVec 384))).bind fun digests =>
        steeredDigestedBody bridge scalar adversary parameter auxiliary datum mask
          (digestField digests) digests

/-- Replacing the nonzero mask by a uniform field element costs `2 / p`. -/
theorem advantage_steeredDigestedGame_steeredMaskedGame_le [FieldCertificate] [GroupCertificate]
    (bridge : NonZeroBase → BaseField) (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) :
    advantage (steeredDigestedGame bridge scalar adversary parameter auxiliary)
        (steeredMaskedGame bridge scalar adversary parameter auxiliary) ≤
      2 / (baseFieldModulus : ℝ) :=
  advantage_bind_le_of_le _ _ _ _ fun _ =>
    (advantage_bind_le_totalDifference _ _ _).trans mask_total_difference

/-- The simulated side's game whose hash secrets are a uniform field element per gate, still
read through a fiber of themselves. -/
def steeredFiberedDigestGame [FieldCertificate] [GroupCertificate]
    (bridge : NonZeroBase → BaseField) (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) : PMF Bool :=
  (PMF.uniformOfFintype ReferenceDatum).bind fun datum =>
    (PMF.uniformOfFintype BaseField).bind fun mask =>
      ((PMF.uniformOfFintype (GateValues BaseField)).bind uniformHashFibers).bind fun digests =>
        steeredDigestedBody bridge scalar adversary parameter auxiliary datum mask
          (digestField digests) digests

/-- Replacing the fresh digest of every gate by a uniform field element and a uniform fiber
sample of it costs `1270 * p / 2 ^ 384`. -/
theorem advantage_steeredMaskedGame_steeredFiberedDigestGame_le [FieldCertificate]
    [GroupCertificate] (bridge : NonZeroBase → BaseField) (scalar : NonZeroScalar)
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    advantage (steeredMaskedGame bridge scalar adversary parameter auxiliary)
        (steeredFiberedDigestGame bridge scalar adversary parameter auxiliary) ≤
      1270 * ((baseFieldModulus : ℝ) / 2 ^ 384) := by
  refine advantage_bind_le_of_le _ _ _ _ fun _ => advantage_bind_le_of_le _ _ _ _ fun _ => ?_
  refine (advantage_bind_le_totalDifference _ _ _).trans ?_
  rw [totalDifference_comm]
  exact hashFibers_total_difference

/-- The simulated side's game with the fiber sample taken after the input is chosen, at the
selected outputs. -/
def steeredFiberGame [FieldCertificate] [GroupCertificate] (bridge : NonZeroBase → BaseField)
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    PMF Bool :=
  (PMF.uniformOfFintype ReferenceDatum).bind fun datum =>
    (PMF.uniformOfFintype BaseField).bind fun mask =>
      (PMF.uniformOfFintype (GateValues BaseField)).bind fun hash =>
        steeredFiberedBody bridge scalar adversary parameter auxiliary datum mask hash

/-- Deferring the fiber sample past the first stage and moving it to the selected outputs is
free, steering or no steering: the second stage sees the fibers only through the programming
of the selected labels, and no slot of a gate whose bit is set is programmed from a fiber. -/
theorem steeredFiberedDigestGame_eq_steeredFiberGame [FieldCertificate] [GroupCertificate]
    (bridge : NonZeroBase → BaseField) (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) :
    steeredFiberedDigestGame bridge scalar adversary parameter auxiliary =
      steeredFiberGame bridge scalar adversary parameter auxiliary := by
  unfold steeredFiberedDigestGame steeredFiberGame
  refine congrArg (PMF.bind _) (funext fun datum => ?_)
  refine congrArg (PMF.bind _) (funext fun mask => ?_)
  rw [PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun hash => ?_)
  have reduce : ((uniformHashFibers hash).bind fun digests =>
      steeredDigestedBody bridge scalar adversary parameter auxiliary datum mask
        (digestField digests) digests) =
      (uniformHashFibers hash).bind fun fibers =>
        steeredDigestedBody bridge scalar adversary parameter auxiliary datum mask hash fibers :=
    bind_congr_support fun fibers member =>
      congrArg (fun outputs => steeredDigestedBody bridge scalar adversary parameter auxiliary
        datum mask outputs fibers) (digestField_of_mem_uniformHashFibers hash fibers member)
  rw [reduce]
  unfold steeredDigestedBody steeredFiberedBody
  rw [PMF.bind_comm (uniformHashFibers hash)
    (loggedFirstStage adversary parameter auxiliary (referenceCircuit bridge datum mask hash)
      (referenceView datum))
    fun fibers outcome =>
      (selectedSimulatedStageTwo adversary parameter auxiliary
        (referenceCircuit bridge datum mask hash) outcome.1.1
        (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2
        (encodeCoordinates outcome.1.1 (referenceRaw datum mask hash)).hash fibers
        (stageTwoState (referenceView datum) outcome.2
          (referenceCircuit bridge datum mask hash).1 (referenceCarrier datum)
          (referenceKey datum))).map Prod.fst]
  refine congrArg (PMF.bind _) (funext fun outcome => ?_)
  exact uniformHashFibers_selected outcome.1.1 (referenceRaw datum mask hash)
    (stageTwoState (referenceView datum) outcome.2
      (referenceCircuit bridge datum mask hash).1 (referenceCarrier datum) (referenceKey datum))
    (simulatedStageTwo adversary parameter auxiliary (referenceCircuit bridge datum mask hash)
      outcome.1.1 (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2)
    _ fun _ => rfl

/-! ### The steered reference game `R(u)` -/

/-- One round of the steered reference game: the reference game's round, except that its
second stage is the simulator's -- the honest labels, then the steering -- on the view the
reference game programs at the selected labels. -/
def steeredReferenceRound [FieldCertificate] [GroupCertificate]
    (bridge : NonZeroBase → BaseField) (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (view : View) (key : InputMacKey)
    (carrier : NonZeroBase) (raw : Coordinates) : PMF Bool :=
  (loggedFirstStage adversary parameter auxiliary
      (raw.table (bridge carrier) key, carrierBits carrier) view).bind fun outcome =>
    (uniformHashFibers (encodeCoordinates outcome.1.1 raw).hash).bind fun fibers =>
      (selectedSimulatedStageTwo adversary parameter auxiliary
        (raw.table (bridge carrier) key, carrierBits carrier) outcome.1.1
        (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2
        (encodeCoordinates outcome.1.1 raw).hash fibers
        (stageTwoState view outcome.2 (raw.table (bridge carrier) key) carrier key)).map
        Prod.fst

/-- The steered reference game `R(bridge)`: the reference game of `bridge` plus the
steering, written in the split sample shape `referenceGame_eq_split` puts the reference game
into, so that step 7 can compare the two rounds under one sample. -/
def steeredReferenceGame [FieldCertificate] [GroupCertificate]
    (bridge : NonZeroBase → BaseField) (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) : PMF Bool :=
  (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
    (PMF.uniformOfFintype InputMacKey).bind fun key =>
      (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
          (PMF.uniformOfFintype Coordinates).bind fun raw =>
            steeredReferenceRound bridge scalar adversary parameter auxiliary
              (oracle, tape.encOracle, tape.hashOracle) key carrier raw

/-- Step 2 of the simulated side ends at the steered reference game of the sample's own
bridge key. -/
theorem steeredFiberGame_eq_steeredReferenceGame [FieldCertificate] [GroupCertificate]
    (bridge : NonZeroBase → BaseField) (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) :
    steeredFiberGame bridge scalar adversary parameter auxiliary =
      steeredReferenceGame bridge scalar adversary parameter auxiliary := by
  have left : steeredFiberGame bridge scalar adversary parameter auxiliary =
      (PMF.uniformOfFintype (ReferenceDatum × BaseField × GateValues BaseField)).bind
        fun sample => steeredFiberedBody bridge scalar adversary parameter auxiliary sample.1
          sample.2.1 sample.2.2 := by
    unfold steeredFiberGame
    simp only [uniformOfFintype_bind_prod]
  have right : steeredReferenceGame bridge scalar adversary parameter auxiliary =
      (PMF.uniformOfFintype (Garbling.Randomness × InputMacKey ×
        PermutationOracle FixedKeyIndex Block × NonZeroBase × Coordinates)).bind fun sample =>
          steeredReferenceRound bridge scalar adversary parameter auxiliary
            (sample.2.2.1, sample.1.encOracle, sample.1.hashOracle) sample.2.1 sample.2.2.2.1
            sample.2.2.2.2 := by
    unfold steeredReferenceGame
    simp only [uniformOfFintype_bind_prod]
  rw [left, right, ← uniformOfFintype_bind_bijection referenceSampleEquiv]
  rfl

/-! ### The simulated side of the chain, up to the steering -/

/-- Step 2 of the chain on the simulated side: replacing the nonzero mask and the fresh
digest family by the reference game's own coordinates and fiber sample costs one side's
share of the one-time budget. -/
theorem advantage_steeredDigested_steeredReferenceGame_le [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    advantage (steeredDigested scalar adversary parameter auxiliary)
        ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
          steeredReferenceGame (fun _ => bridgeKey.value) scalar adversary parameter
            auxiliary) ≤ sideOneTime := by
  have identify : ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        steeredReferenceGame (fun _ => bridgeKey.value) scalar adversary parameter auxiliary) =
      (PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        steeredFiberedDigestGame (fun _ => bridgeKey.value) scalar adversary parameter
          auxiliary :=
    congrArg (PMF.bind _) (funext fun bridgeKey =>
      ((steeredFiberedDigestGame_eq_steeredFiberGame (fun _ => bridgeKey.value) scalar adversary
        parameter auxiliary).trans (steeredFiberGame_eq_steeredReferenceGame
          (fun _ => bridgeKey.value) scalar adversary parameter auxiliary)).symm)
  rw [steeredDigested_eq, identify]
  unfold sideOneTime
  refine advantage_trans _ ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
    steeredMaskedGame (fun _ => bridgeKey.value) scalar adversary parameter auxiliary) _ _ _
    (advantage_bind_le_of_le _ _ _ _ fun bridgeKey =>
      advantage_steeredDigestedGame_steeredMaskedGame_le (fun _ => bridgeKey.value) scalar
        adversary parameter auxiliary)
    (advantage_bind_le_of_le _ _ _ _ fun bridgeKey =>
      advantage_steeredMaskedGame_steeredFiberedDigestGame_le (fun _ => bridgeKey.value) scalar
        adversary parameter auxiliary)

/-- The simulated side of the chain, up to the steering: the simulated game is within
`4 (q₁ + q₂) / 2 ^ 128` plus one side's one-time budget of the steered reference game of the
tape's own bridge key `u`. Steps 4, 5 and 6 supply the per-query term, the simulated side's
own copy of step 2 the one-time term. Identifying `R(u)` plus the steering with
`R(carrier / scalar)` is step 7 and is not done here. -/
theorem advantage_simulatedGame_steeredReferenceGame_le [FieldCertificate] [GroupCertificate]
    (adversary : Adversary) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    advantage
        (idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) simulator idealOracle
          adversary parameter scalar auxiliary)
        ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
          steeredReferenceGame (fun _ => bridgeKey.value) scalar adversary parameter
            auxiliary) ≤
      4 * ((adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 + sideOneTime :=
  advantage_trans _ _ _ _ _
    (advantage_simulatedGame_steeredDigested_le adversary parameter scalar auxiliary)
    (advantage_steeredDigested_steeredReferenceGame_le scalar adversary parameter auxiliary)

end

end Kriterion.ArgoMAC.Security
