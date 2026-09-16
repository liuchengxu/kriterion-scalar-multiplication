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

end

end Kriterion.ArgoMAC.Security
