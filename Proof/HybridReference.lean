/-
This file finishes the hybrid side of the chain. The two oracle hops left the
hybrid game in the reference game's shape but still carrying the secrets of the
reparametrisation: a nonzero curve mask, and one fresh 384-bit digest per gate
standing both for the table's hash secret and for the reference game's fiber
sample. Step 2 of the chain replaces them. The mask becomes a uniform field
element, at total difference `2 / p`; the digest family becomes a uniform field
element per gate followed by a uniform fiber sample of it, at total difference
`1270 * p / 2 ^ 384`. The fiber sample can then be deferred past the first
stage, where the reference game takes it at the *selected* outputs rather than
at the sampled hash secrets. The two families differ exactly at the gates whose
input bit is set, and no slot of such a gate is programmed from a fiber, so the
marginal lemma for product laws closes the gap for free.
-/

import Proof.GateProduct
import Proof.HybridChain

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

noncomputable section

/-! ### Uniform samples of a product -/

/-- A uniform sample may be reindexed along a bijection. -/
theorem uniformOfFintype_bind_bijection {Source Target Result : Type} [Fintype Source]
    [Nonempty Source] [Fintype Target] [Nonempty Target] (bijection : Source ≃ Target)
    (continuation : Target → PMF Result) :
    ((PMF.uniformOfFintype Source).bind fun source => continuation (bijection source)) =
      (PMF.uniformOfFintype Target).bind continuation := by
  rw [← uniformOfFintype_map_bijection bijection, PMF.bind_map]
  rfl

/-- The key-free sample of the hybrid side is a uniform sample of its product type. -/
theorem hybridData_eq_uniform : hybridData = PMF.uniformOfFintype HybridDatum := by
  have pureForm : hybridData =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
          (PMF.uniformOfFintype (GateValues (BitVec 384) ×
              GateValues BitAdaptor.Ciphertext)).bind fun secrets =>
            (PMF.uniformOfFintype (NonZeroBase × BaseField × BaseField)).bind fun curve =>
              (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
                PMF.pure ((tape, oracle, secrets, curve, carrier) : HybridDatum) := by
    conv_lhs => rw [← PMF.bind_pure hybridData]
    exact hybridData_bind PMF.pure
  rw [pureForm]
  simp only [uniformOfFintype_bind_prod]
  exact PMF.bind_pure _

/-! ### The samples the one-time hops do not touch -/

/-- The samples of the reference-shaped game other than the mask and the hash secrets:
the label key, the tape's unread oracles, the unprogrammed fixed-key oracle, the pads, the
two curve secrets and the carrier. -/
abbrev ReferenceDatum :=
  InputMacKey × Garbling.Randomness × PermutationOracle FixedKeyIndex Block ×
    GateValues BitAdaptor.Ciphertext × (BaseField × BaseField) × NonZeroBase

/-- The label key of one sample. -/
def referenceKey (datum : ReferenceDatum) : InputMacKey := datum.1

/-- The unprogrammed view of one sample. -/
def referenceView (datum : ReferenceDatum) : View :=
  (datum.2.2.1, datum.2.1.encOracle, datum.2.1.hashOracle)

/-- The pads of one sample. -/
def referencePads (datum : ReferenceDatum) : GateValues BitAdaptor.Ciphertext := datum.2.2.2.1

/-- The first curve secret of one sample. -/
def referenceR1 (datum : ReferenceDatum) : BaseField := datum.2.2.2.2.1.1

/-- The second curve secret of one sample. -/
def referenceR2 (datum : ReferenceDatum) : BaseField := datum.2.2.2.2.1.2

/-- The carrier of one sample. -/
def referenceCarrier (datum : ReferenceDatum) : NonZeroBase := datum.2.2.2.2.2

/-- The reference coordinates of one sample, one mask and one hash family. -/
def referenceRaw (datum : ReferenceDatum) (mask : BaseField) (hash : GateValues BaseField) :
    Coordinates :=
  ⟨mask, referenceR1 datum, referenceR2 datum, hash, referencePads datum⟩

/-- The public value of one sample: the reference table of the carrier's bridge key. -/
def referenceCircuit [FieldCertificate] (scalar : NonZeroScalar) (datum : ReferenceDatum)
    (mask : BaseField) (hash : GateValues BaseField) : Garbling.Public :=
  (Coordinates.table (((mulScalar scalar).symm (referenceCarrier datum)).value)
      (referenceKey datum) (referenceRaw datum mask hash),
    carrierBits (referenceCarrier datum))

/-! ### The two bodies of step 2 -/

/-- The reference-shaped round with the fiber family already fixed before the first stage:
this is what the two oracle hops left. -/
def digestedBody [FieldCertificate] (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (datum : ReferenceDatum) (mask : BaseField)
    (hash : GateValues BaseField) (fibers : GateValues (BitVec 384)) : PMF Bool :=
  (loggedFirstStage adversary parameter auxiliary (referenceCircuit scalar datum mask hash)
      (referenceView datum)).bind fun outcome =>
    (selectedStageTwo adversary parameter auxiliary (referenceCircuit scalar datum mask hash)
      outcome.1.1 outcome.1.2
      (encodeCoordinates outcome.1.1 (referenceRaw datum mask hash)).hash fibers
      (stageTwoState (referenceView datum) outcome.2
        (referenceCircuit scalar datum mask hash).1 (referenceCarrier datum)
        (referenceKey datum))).map Prod.fst

/-- The reference-shaped round with the fiber family sampled after the input is chosen, at
the selected outputs: this is the reference game. -/
def fiberedBody [FieldCertificate] (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (datum : ReferenceDatum) (mask : BaseField)
    (hash : GateValues BaseField) : PMF Bool :=
  (loggedFirstStage adversary parameter auxiliary (referenceCircuit scalar datum mask hash)
      (referenceView datum)).bind fun outcome =>
    (uniformHashFibers
        (encodeCoordinates outcome.1.1 (referenceRaw datum mask hash)).hash).bind fun fibers =>
      (selectedStageTwo adversary parameter auxiliary (referenceCircuit scalar datum mask hash)
        outcome.1.1 outcome.1.2
        (encodeCoordinates outcome.1.1 (referenceRaw datum mask hash)).hash fibers
        (stageTwoState (referenceView datum) outcome.2
          (referenceCircuit scalar datum mask hash).1 (referenceCarrier datum)
          (referenceKey datum))).map Prod.fst

/-! ### The hybrid side in the shape of step 2 -/

/-- The reference-shaped sample the hybrid side's own sample names. -/
def referenceOf (key : InputMacKey) (datum : HybridDatum) : ReferenceDatum :=
  (key, datum.1, datum.2.1, hybridPads datum, (hybridR1 datum, hybridR2 datum),
    hybridCarrier datum)

theorem referenceView_referenceOf (key : InputMacKey) (datum : HybridDatum) :
    referenceView (referenceOf key datum) = hybridView datum := rfl

theorem referenceRaw_referenceOf (key : InputMacKey) (datum : HybridDatum) :
    referenceRaw (referenceOf key datum) (hybridMask datum)
        (digestField (hybridDigests datum)) = hybridRaw datum := rfl

/-- The hybrid side's public value is the reference-shaped one: the reference table ignores
the label key, so the key the second stage uses may be read off the sample. -/
theorem hybridCircuit_eq_referenceCircuit [FieldCertificate] (scalar : NonZeroScalar)
    (key : InputMacKey) (datum : HybridDatum) :
    hybridCircuit scalar datum =
      referenceCircuit scalar (referenceOf key datum) (hybridMask datum)
        (digestField (hybridDigests datum)) :=
  congrArg (fun table => (table, carrierBits (hybridCarrier datum)))
    (Coordinates.table_key _ _ _ _)

/-- The game the two oracle hops left, with the mask and the digests floated out. -/
def digestedGame [FieldCertificate] (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) : PMF Bool :=
  (PMF.uniformOfFintype ReferenceDatum).bind fun datum =>
    ((PMF.uniformOfFintype NonZeroBase).map NonZeroBase.value).bind fun mask =>
      (PMF.uniformOfFintype (GateValues (BitVec 384))).bind fun digests =>
        digestedBody scalar adversary parameter auxiliary datum mask (digestField digests) digests

/-- Floating the mask and the digests out of the hybrid side's sample. -/
def digestedSampleEquiv :
    InputMacKey × HybridDatum ≃ ReferenceDatum × NonZeroBase × GateValues (BitVec 384) where
  toFun sample := (referenceOf sample.1 sample.2, sample.2.2.2.2.1.1, hybridDigests sample.2)
  invFun sample :=
    (sample.1.1, (sample.1.2.1, sample.1.2.2.1, (sample.2.2, referencePads sample.1),
      (sample.2.1, referenceR1 sample.1, referenceR2 sample.1), referenceCarrier sample.1))
  left_inv := by
    rintro ⟨key, tape, oracle, ⟨digests, pads⟩, ⟨mask, r1, r2⟩, carrier⟩
    rfl
  right_inv := by
    rintro ⟨⟨key, tape, oracle, pads, ⟨r1, r2⟩, carrier⟩, mask, digests⟩
    rfl

/-- The hybrid side after both oracle hops, with the mask and the digests floated out of
the sample so that step 2 can replace them. -/
theorem digestedReference_eq [FieldCertificate] (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) :
    digestedReference scalar adversary parameter auxiliary =
      digestedGame scalar adversary parameter auxiliary := by
  have body : ∀ (key : InputMacKey) (datum : HybridDatum),
      ((loggedFirstStage adversary parameter auxiliary (hybridCircuit scalar datum)
          (hybridView datum)).bind fun outcome =>
        (selectedStageTwo adversary parameter auxiliary (hybridCircuit scalar datum) outcome.1.1
          outcome.1.2 (encodeCoordinates outcome.1.1 (hybridRaw datum)).hash
          (hybridDigests datum)
          (stageTwoState (hybridView datum) outcome.2 (hybridCircuit scalar datum).1
            (hybridCarrier datum) key)).map Prod.fst) =
        digestedBody scalar adversary parameter auxiliary (referenceOf key datum)
          (hybridMask datum) (digestField (hybridDigests datum)) (hybridDigests datum) := by
    intro key datum
    rw [hybridCircuit_eq_referenceCircuit scalar key datum]
    rfl
  have left : digestedReference scalar adversary parameter auxiliary =
      (PMF.uniformOfFintype (InputMacKey × HybridDatum)).bind fun sample =>
        digestedBody scalar adversary parameter auxiliary (referenceOf sample.1 sample.2)
          (hybridMask sample.2) (digestField (hybridDigests sample.2))
          (hybridDigests sample.2) := by
    unfold digestedReference
    rw [hybridData_eq_uniform]
    rw [show ((PMF.uniformOfFintype InputMacKey).bind fun key =>
        (PMF.uniformOfFintype HybridDatum).bind fun datum =>
          (loggedFirstStage adversary parameter auxiliary (hybridCircuit scalar datum)
              (hybridView datum)).bind fun outcome =>
            (selectedStageTwo adversary parameter auxiliary (hybridCircuit scalar datum)
              outcome.1.1 outcome.1.2 (encodeCoordinates outcome.1.1 (hybridRaw datum)).hash
              (hybridDigests datum)
              (stageTwoState (hybridView datum) outcome.2 (hybridCircuit scalar datum).1
                (hybridCarrier datum) key)).map Prod.fst) =
        ((PMF.uniformOfFintype InputMacKey).bind fun key =>
          (PMF.uniformOfFintype HybridDatum).bind fun datum =>
            digestedBody scalar adversary parameter auxiliary (referenceOf key datum)
              (hybridMask datum) (digestField (hybridDigests datum)) (hybridDigests datum)) from
      congrArg (PMF.bind _) (funext fun key =>
        congrArg (PMF.bind _) (funext fun datum => body key datum))]
    exact uniformOfFintype_bind_prod fun key datum =>
      digestedBody scalar adversary parameter auxiliary (referenceOf key datum)
        (hybridMask datum) (digestField (hybridDigests datum)) (hybridDigests datum)
  have right : digestedGame scalar adversary parameter auxiliary =
      (PMF.uniformOfFintype (ReferenceDatum × NonZeroBase ×
        GateValues (BitVec 384))).bind fun sample =>
          digestedBody scalar adversary parameter auxiliary sample.1 sample.2.1.value
            (digestField sample.2.2) sample.2.2 := by
    unfold digestedGame
    have masked : ∀ datum : ReferenceDatum,
        (((PMF.uniformOfFintype NonZeroBase).map NonZeroBase.value).bind fun mask =>
            (PMF.uniformOfFintype (GateValues (BitVec 384))).bind fun digests =>
              digestedBody scalar adversary parameter auxiliary datum mask
                (digestField digests) digests) =
          (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
            (PMF.uniformOfFintype (GateValues (BitVec 384))).bind fun digests =>
              digestedBody scalar adversary parameter auxiliary datum mask.value
                (digestField digests) digests := by
      intro datum
      rw [PMF.bind_map]
      rfl
    rw [congrArg (PMF.bind _) (funext masked)]
    rw [congrArg (PMF.bind (PMF.uniformOfFintype ReferenceDatum)) (funext fun datum =>
      uniformOfFintype_bind_prod fun (mask : NonZeroBase) (digests : GateValues (BitVec 384)) =>
        digestedBody scalar adversary parameter auxiliary datum mask.value
          (digestField digests) digests)]
    exact uniformOfFintype_bind_prod fun (datum : ReferenceDatum)
      (pair : NonZeroBase × GateValues (BitVec 384)) =>
        digestedBody scalar adversary parameter auxiliary datum pair.1.value
          (digestField pair.2) pair.2
  rw [left, right, ← uniformOfFintype_bind_bijection digestedSampleEquiv]
  rfl

/-! ### Step 2, first hop: the nonzero mask becomes a uniform field element -/

/-- The game with the curve mask uniform over the whole field. -/
def maskedGame [FieldCertificate] (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) : PMF Bool :=
  (PMF.uniformOfFintype ReferenceDatum).bind fun datum =>
    (PMF.uniformOfFintype BaseField).bind fun mask =>
      (PMF.uniformOfFintype (GateValues (BitVec 384))).bind fun digests =>
        digestedBody scalar adversary parameter auxiliary datum mask (digestField digests) digests

/-- Replacing the nonzero mask by a uniform field element costs `2 / p`. -/
theorem advantage_digestedGame_maskedGame_le [FieldCertificate] (scalar : NonZeroScalar)
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    advantage (digestedGame scalar adversary parameter auxiliary)
        (maskedGame scalar adversary parameter auxiliary) ≤ 2 / (baseFieldModulus : ℝ) :=
  advantage_bind_le_of_le _ _ _ _ fun _ =>
    (advantage_bind_le_totalDifference _ _ _).trans mask_total_difference

/-! ### Step 2, second hop: the digests become a field element and a fiber sample -/

/-- The game whose hash secrets are a uniform field element per gate, still read through a
fiber of themselves. -/
def fiberedDigestGame [FieldCertificate] (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) : PMF Bool :=
  (PMF.uniformOfFintype ReferenceDatum).bind fun datum =>
    (PMF.uniformOfFintype BaseField).bind fun mask =>
      ((PMF.uniformOfFintype (GateValues BaseField)).bind uniformHashFibers).bind fun digests =>
        digestedBody scalar adversary parameter auxiliary datum mask (digestField digests) digests

/-- Replacing the fresh digest of every gate by a uniform field element and a uniform fiber
sample of it costs `1270 * p / 2 ^ 384`. -/
theorem advantage_maskedGame_fiberedDigestGame_le [FieldCertificate] (scalar : NonZeroScalar)
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    advantage (maskedGame scalar adversary parameter auxiliary)
        (fiberedDigestGame scalar adversary parameter auxiliary) ≤
      1270 * ((baseFieldModulus : ℝ) / 2 ^ 384) := by
  refine advantage_bind_le_of_le _ _ _ _ fun _ => advantage_bind_le_of_le _ _ _ _ fun _ => ?_
  refine (advantage_bind_le_totalDifference _ _ _).trans ?_
  rw [totalDifference_comm]
  exact hashFibers_total_difference

/-! ### Step 2, the free half: deferring the fiber sample to the selected outputs -/

/-- The digests of a fiber sample reduce to the outputs the sample was taken at. -/
theorem digestField_of_mem_uniformHashFibers (outputs : GateValues BaseField)
    (fibers : GateValues (BitVec 384))
    (member : fibers ∈ (uniformHashFibers outputs).support) :
    digestField fibers = outputs := by
  unfold uniformHashFibers at member
  rw [PMF.support_map] at member
  obtain ⟨element, _, rfl⟩ := member
  funext adaptor position
  exact element.property adaptor position

/-- The reference game programs nothing from the fiber of a gate whose input bit is set: its
hash slots read the label the input leaves unselected. -/
theorem selectedPrograms_setGate (key : InputMacKey) (input : AffineInput)
    (outputs : GateValues BaseField) (rows : GateValues BitAdaptor.Ciphertext)
    (fibers : GateValues (BitVec 384)) (gate : Gate) (value : BitVec 384)
    (bit : inputBits input gate.1 gate.2 = true) :
    selectedPrograms key input outputs rows (setGate gate value fibers) =
      selectedPrograms key input outputs rows fibers := by
  funext index
  obtain ⟨adaptor, position, slot⟩ := index
  cases slot with
  | hash chunk =>
    rw [selectedPrograms_hash, selectedPrograms_hash]
    cases set : inputBits input adaptor position with
    | true => rw [if_pos rfl, if_pos rfl]
    | false =>
      have other : (adaptor, position) ≠ gate := by
        intro equal
        rw [show adaptor = gate.1 from congrArg Prod.fst equal,
          show position = gate.2 from congrArg Prod.snd equal, bit] at set
        exact Bool.noConfusion set
      rw [if_neg (by simp), if_neg (by simp), setGate_apply, if_neg other]
  | pad chunk => rw [selectedPrograms_pad, selectedPrograms_pad]

/-- The reference-shaped second stage never reads the fiber of a gate whose input bit is
set. -/
theorem selectedStageTwo_setGate (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (circuit : Garbling.Public) (input : AffineInput) (advState : adversary.State)
    (outputs : GateValues BaseField) (fibers : GateValues (BitVec 384)) (state : State)
    (gate : Gate) (value : BitVec 384) (bit : inputBits input gate.1 gate.2 = true) :
    selectedStageTwo adversary parameter auxiliary circuit input advState outputs
        (setGate gate value fibers) state =
      selectedStageTwo adversary parameter auxiliary circuit input advState outputs fibers
        state := by
  unfold selectedStageTwo programSelected
  rw [selectedPrograms_setGate state.inputMacKey input outputs (tableRow state.table) fibers gate
    value bit]

/-- The reference game's fiber sample is taken at the selected outputs, which agree with the
sampled hash secrets off the gates whose input bit is set. Those gates' fibers are read
nowhere, so the two samples give the same game. -/
theorem uniformHashFibers_selected (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (circuit : Garbling.Public) (input : AffineInput) (advState : adversary.State)
    (raw : Coordinates) (state : State)
    (continuation : GateValues (BitVec 384) → PMF (Bool × List Query))
    (body : ∀ fibers, continuation fibers =
      selectedStageTwo adversary parameter auxiliary circuit input advState
        (encodeCoordinates input raw).hash fibers state) :
    ((uniformHashFibers raw.hash).bind fun fibers => (continuation fibers).map Prod.fst) =
      (uniformHashFibers (encodeCoordinates input raw).hash).bind fun fibers =>
        (continuation fibers).map Prod.fst := by
  refine uniformHashFibers_bind_congr raw.hash (encodeCoordinates input raw).hash
    (Finset.univ.filter fun gate : Gate => inputBits input gate.1 gate.2 = true) _ ?_ ?_
  · intro gate notMember
    have unset : inputBits input gate.1 gate.2 = false := by
      by_cases set : inputBits input gate.1 gate.2 = true
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ gate, set⟩) notMember
      · simpa using set
    simp [encodeCoordinates, selectOutput, unset]
  · intro gate member fibers value
    have set : inputBits input gate.1 gate.2 = true := (Finset.mem_filter.mp member).2
    rw [body, body, selectedStageTwo_setGate adversary parameter auxiliary circuit input advState
      (encodeCoordinates input raw).hash fibers state gate value set]

/-- The reference game itself: the fiber sample is taken after the input is chosen, at the
selected outputs. -/
def fiberGame [FieldCertificate] (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) : PMF Bool :=
  (PMF.uniformOfFintype ReferenceDatum).bind fun datum =>
    (PMF.uniformOfFintype BaseField).bind fun mask =>
      (PMF.uniformOfFintype (GateValues BaseField)).bind fun hash =>
        fiberedBody scalar adversary parameter auxiliary datum mask hash

/-- Deferring the fiber sample past the first stage and moving it to the selected outputs is
free. -/
theorem fiberedDigestGame_eq_fiberGame [FieldCertificate] (scalar : NonZeroScalar)
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    fiberedDigestGame scalar adversary parameter auxiliary =
      fiberGame scalar adversary parameter auxiliary := by
  unfold fiberedDigestGame fiberGame
  refine congrArg (PMF.bind _) (funext fun datum => ?_)
  refine congrArg (PMF.bind _) (funext fun mask => ?_)
  rw [PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun hash => ?_)
  have reduce : ((uniformHashFibers hash).bind fun digests =>
      digestedBody scalar adversary parameter auxiliary datum mask (digestField digests)
        digests) =
      (uniformHashFibers hash).bind fun fibers =>
        digestedBody scalar adversary parameter auxiliary datum mask hash fibers :=
    bind_congr_support fun fibers member =>
      congrArg (fun outputs => digestedBody scalar adversary parameter auxiliary datum mask
        outputs fibers) (digestField_of_mem_uniformHashFibers hash fibers member)
  rw [reduce]
  unfold digestedBody fiberedBody
  rw [PMF.bind_comm (uniformHashFibers hash)
    (loggedFirstStage adversary parameter auxiliary (referenceCircuit scalar datum mask hash)
      (referenceView datum))
    fun fibers outcome =>
      (selectedStageTwo adversary parameter auxiliary
        (referenceCircuit scalar datum mask hash) outcome.1.1 outcome.1.2
        (encodeCoordinates outcome.1.1 (referenceRaw datum mask hash)).hash fibers
        (stageTwoState (referenceView datum) outcome.2
          (referenceCircuit scalar datum mask hash).1 (referenceCarrier datum)
          (referenceKey datum))).map Prod.fst]
  refine congrArg (PMF.bind _) (funext fun outcome => ?_)
  exact uniformHashFibers_selected adversary parameter auxiliary
    (referenceCircuit scalar datum mask hash) outcome.1.1 outcome.1.2
    (referenceRaw datum mask hash)
    (stageTwoState (referenceView datum) outcome.2
      (referenceCircuit scalar datum mask hash).1 (referenceCarrier datum) (referenceKey datum))
    _ fun _ => rfl

/-! ### The identification with the reference game -/

/-- One round of the reference game on explicit coordinates: the first stage runs on the
unprogrammed view, the fiber sample is taken at the selected outputs of the chosen input,
and the second stage runs on the view programmed at the selected labels. -/
def referenceRound (bridge : NonZeroBase → BaseField) (adversary : Adversary) (parameter : Nat)
    (auxiliary : Unit) (view : View) (key : InputMacKey) (carrier : NonZeroBase)
    (raw : Coordinates) : PMF Bool :=
  (loggedFirstStage adversary parameter auxiliary
      (raw.table (bridge carrier) key, carrierBits carrier) view).bind fun outcome =>
    (uniformHashFibers (encodeCoordinates outcome.1.1 raw).hash).bind fun fibers =>
      (selectedStageTwo adversary parameter auxiliary
        (raw.table (bridge carrier) key, carrierBits carrier) outcome.1.1 outcome.1.2
        (encodeCoordinates outcome.1.1 raw).hash fibers
        (stageTwoState view outcome.2 (raw.table (bridge carrier) key) carrier key)).map
        Prod.fst

/-- The reference game is one round of `referenceRound` on a uniform tape, carrier and raw
coordinates. -/
theorem referenceGame_eq (bridge : NonZeroBase → BaseField) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) :
    referenceGame bridge adversary parameter auxiliary =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
          (PMF.uniformOfFintype Coordinates).bind fun raw =>
            referenceRound bridge adversary parameter auxiliary (Garbling.evaluationOracle tape)
              tape.inputMacKey carrier raw := by
  unfold referenceGame
  refine congrArg (PMF.bind _) (funext fun tape => ?_)
  refine congrArg (PMF.bind _) (funext fun carrier => ?_)
  refine congrArg (PMF.bind _) (funext fun raw => ?_)
  have conditioned : (((adversary.chooseInput parameter
        (raw.table (bridge carrier) tape.inputMacKey, carrierBits carrier) auxiliary).run
        idealOracle (initialState tape (raw.table (bridge carrier) tape.inputMacKey)
          carrier)).bind fun selected =>
      referenceStage2 adversary parameter auxiliary
        (raw.table (bridge carrier) tape.inputMacKey, carrierBits carrier)
        (encodeCoordinates selected.1.1 raw).hash selected) =
      (((adversary.chooseInput parameter
        (raw.table (bridge carrier) tape.inputMacKey, carrierBits carrier) auxiliary).run
        idealOracle (initialState tape (raw.table (bridge carrier) tape.inputMacKey)
          carrier)).bind fun selected =>
      referenceStage2 adversary parameter auxiliary
        (raw.table (bridge carrier) tape.inputMacKey, carrierBits carrier)
        (encodeCoordinates selected.1.1 raw).hash
        (selected.1, stageTwoState (Garbling.evaluationOracle tape) selected.2.log
          (raw.table (bridge carrier) tape.inputMacKey) carrier tape.inputMacKey)) := by
    refine bind_congr_support fun selected member => ?_
    obtain ⟨sameView, sameTable, sameCarrier, sameKey⟩ :=
      run_idealOracle_support _ _ selected member
    rw [← eq_stageTwoState (Garbling.evaluationOracle tape)
      (raw.table (bridge carrier) tape.inputMacKey) carrier tape.inputMacKey selected.2 sameView
      sameTable sameCarrier sameKey]
  have factor := (PMF.bind_map
    ((adversary.chooseInput parameter (raw.table (bridge carrier) tape.inputMacKey,
        carrierBits carrier) auxiliary).run idealOracle
      (initialState tape (raw.table (bridge carrier) tape.inputMacKey) carrier))
    loggedOutcome
    (fun outcome : (AffineInput × adversary.State) × List Query =>
      referenceStage2 adversary parameter auxiliary
        (raw.table (bridge carrier) tape.inputMacKey, carrierBits carrier)
        (encodeCoordinates outcome.1.1 raw).hash
        (outcome.1, stageTwoState (Garbling.evaluationOracle tape) outcome.2
          (raw.table (bridge carrier) tape.inputMacKey) carrier tape.inputMacKey))).symm
  refine conditioned.trans (factor.trans ?_)
  rw [show initialState tape (raw.table (bridge carrier) tape.inputMacKey) carrier =
      firstState (Garbling.evaluationOracle tape)
        (raw.table (bridge carrier) tape.inputMacKey) carrier tape.inputMacKey from rfl,
    map_loggedOutcome_firstState adversary parameter auxiliary
    (raw.table (bridge carrier) tape.inputMacKey, carrierBits carrier)
    (Garbling.evaluationOracle tape) (raw.table (bridge carrier) tape.inputMacKey) carrier
    tape.inputMacKey]
  refine congrArg (PMF.bind _) (funext fun outcome => ?_)
  unfold referenceStage2 selectedStageTwo hybridStageTwo
  exact congrArg (PMF.bind _) (funext fun fibers => (map_fst_loggedOutcome _).symm)

/-- The reference game with the label key and the fixed-key oracle sampled separately from
the rest of the tape. -/
theorem referenceGame_eq_split (bridge : NonZeroBase → BaseField) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) :
    referenceGame bridge adversary parameter auxiliary =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype InputMacKey).bind fun key =>
          (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
            (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
              (PMF.uniformOfFintype Coordinates).bind fun raw =>
                referenceRound bridge adversary parameter auxiliary
                  (oracle, tape.encOracle, tape.hashOracle) key carrier raw := by
  rw [referenceGame_eq, ← uniform_bind_setOracle, ← uniform_bind_setKey]
  rfl

/-- The reference game's sample as the reference-shaped sample plus the mask and the hash
secrets. -/
def referenceSampleEquiv :
    ReferenceDatum × BaseField × GateValues BaseField ≃
      Garbling.Randomness × InputMacKey × PermutationOracle FixedKeyIndex Block ×
        NonZeroBase × Coordinates where
  toFun sample :=
    (sample.1.2.1, sample.1.1, sample.1.2.2.1, referenceCarrier sample.1,
      referenceRaw sample.1 sample.2.1 sample.2.2)
  invFun sample :=
    ((sample.2.1, sample.1, sample.2.2.1, sample.2.2.2.2.pad,
        (sample.2.2.2.2.r1, sample.2.2.2.2.r2), sample.2.2.2.1),
      sample.2.2.2.2.mask, sample.2.2.2.2.hash)
  left_inv := by
    rintro ⟨⟨key, tape, oracle, pads, ⟨r1, r2⟩, carrier⟩, mask, hash⟩
    rfl
  right_inv := by
    rintro ⟨tape, key, oracle, carrier, ⟨mask, r1, r2, hash, pads⟩⟩
    rfl

/-- Step 2 ends at the reference game of the hybrid side's own bridge key. -/
theorem fiberGame_eq_referenceGame [FieldCertificate] (scalar : NonZeroScalar)
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    fiberGame scalar adversary parameter auxiliary =
      referenceGame (fun carrier => ((mulScalar scalar).symm carrier).value) adversary parameter
        auxiliary := by
  have left : fiberGame scalar adversary parameter auxiliary =
      (PMF.uniformOfFintype (ReferenceDatum × BaseField × GateValues BaseField)).bind
        fun sample => fiberedBody scalar adversary parameter auxiliary sample.1 sample.2.1
          sample.2.2 := by
    unfold fiberGame
    simp only [uniformOfFintype_bind_prod]
  have right : referenceGame (fun carrier => ((mulScalar scalar).symm carrier).value) adversary
        parameter auxiliary =
      (PMF.uniformOfFintype (Garbling.Randomness × InputMacKey ×
        PermutationOracle FixedKeyIndex Block × NonZeroBase × Coordinates)).bind fun sample =>
          referenceRound (fun carrier => ((mulScalar scalar).symm carrier).value) adversary
            parameter auxiliary (sample.2.2.1, sample.1.encOracle, sample.1.hashOracle)
            sample.2.1 sample.2.2.2.1 sample.2.2.2.2 := by
    rw [referenceGame_eq_split]
    simp only [uniformOfFintype_bind_prod]
  rw [left, right, ← uniformOfFintype_bind_bijection referenceSampleEquiv]
  rfl

/-! ### Step 2 of the chain, and the whole hybrid side -/

/-- Step 2 of the chain on the hybrid side: replacing the nonzero mask and the fresh digest
family by the reference game's own coordinates and fiber sample costs one side's share of
the one-time budget. -/
theorem advantage_digestedReference_referenceGame_le [FieldCertificate] (scalar : NonZeroScalar)
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    advantage (digestedReference scalar adversary parameter auxiliary)
        (referenceGame (fun carrier => ((mulScalar scalar).symm carrier).value) adversary
          parameter auxiliary) ≤ sideOneTime := by
  rw [digestedReference_eq, ← fiberGame_eq_referenceGame, ← fiberedDigestGame_eq_fiberGame]
  unfold sideOneTime
  exact advantage_trans _ _ _ _ _
    (advantage_digestedGame_maskedGame_le scalar adversary parameter auxiliary)
    (advantage_maskedGame_fiberedDigestGame_le scalar adversary parameter auxiliary)

/-- The hybrid side of the chain, complete: the hybrid game is within `4 (q₁ + q₂) / 2 ^ 128`
plus one side's one-time budget of the reference game of its own bridge key `carrier /
scalar`. Steps 1 and 3 supply the per-query term, step 2 the one-time term. -/
theorem advantage_hybridGame_referenceGame_le [FieldCertificate] [GroupCertificate]
    (adversary : Adversary) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    advantage
        (idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) (hybridSimulator scalar)
          idealOracle adversary parameter scalar auxiliary)
        (referenceGame (fun carrier => ((mulScalar scalar).symm carrier).value) adversary
          parameter auxiliary) ≤
      4 * ((adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 + sideOneTime :=
  advantage_trans _ _ _ _ _
    (advantage_hybridGame_digestedReference_le adversary parameter scalar auxiliary)
    (advantage_digestedReference_referenceGame_le scalar adversary parameter auxiliary)

end

end Kriterion.ArgoMAC.Security
