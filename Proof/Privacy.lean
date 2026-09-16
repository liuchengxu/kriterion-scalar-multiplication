/-
This file states the adaptive-privacy obligation for the scheme and reduces it
to two named lemmas. The reduction and the first lemma are proved; the second
lemma is the remaining obligation.

The hybrid game is the real game written in the simulator's shape: its first
stage samples the same tape and carrier as the simulator but garbles the curve
table for the bridge key `carrier / scalar`, so the honest labels already
release `carrier / scalar` and no programming is needed. The first lemma is the
marginal match: the real game equals the hybrid game. The second lemma is
steering invisibility: the hybrid game and the simulated game differ only where
the adversary hits a programmed or hidden label point.
-/

import Proof.Simulator
import Solution

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

/-- The fixed public byte count. -/
def ciphertextBytes : Nat := 40768

noncomputable section

/-- The hybrid simulator knows the scalar. It garbles honestly for the bridge key
`carrier / scalar` and never programs the oracle. -/
def hybridSimulator [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar) :
    Simulator AffineInput (Option Point) Garbling.Public LamportSignature Nat State where
  simulateGarble _ _ :=
    (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
      (PMF.uniformOfFintype NonZeroBase).map fun carrier =>
        let table := CurveMembership.garble (carrier.value * (scalarAsBase scalar).value⁻¹)
          tape.curveMask.value tape.curveR1 tape.curveR2 (curveOracles tape.fixedKeyOracle)
          tape.inputMacKey
        ((table, carrierBits carrier), initialState tape table carrier)
  simulateEncode state input _ :=
    PMF.pure (Lamport.selectedLabels (state.inputMacKey.encodeAffine input), state)

/-- The real tape law of the obligation. -/
abbrev realTape (witness : Garbling.Randomness) : Nat → PMF Garbling.Randomness :=
  @uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance) witness

/-! ### Uniform sampling facts -/

/-- Two finite-type instances give the same uniform law. -/
theorem uniformOfFintype_congr {Value : Type} (first second : Fintype Value) [Nonempty Value] :
    @PMF.uniformOfFintype Value first _ = @PMF.uniformOfFintype Value second _ := by
  cases Subsingleton.elim first second
  rfl

/-- A uniform sample composed with a bijection is a uniform sample. -/
theorem uniformOfFintype_bind_equiv {Value Result : Type} [Fintype Value] [Nonempty Value]
    (bijection : Value ≃ Value) (continuation : Value → PMF Result) :
    ((PMF.uniformOfFintype Value).bind fun value => continuation (bijection value)) =
      (PMF.uniformOfFintype Value).bind continuation := by
  ext result
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  exact bijection.sum_comp fun value => (Fintype.card Value : ENNReal)⁻¹ * continuation value result

/-- Two independent uniform samples are one uniform sample of the product. -/
theorem uniformOfFintype_bind_prod {Left Right Result : Type} [Fintype Left] [Nonempty Left]
    [Fintype Right] [Nonempty Right] (continuation : Left → Right → PMF Result) :
    ((PMF.uniformOfFintype Left).bind fun left =>
        (PMF.uniformOfFintype Right).bind fun right => continuation left right) =
      (PMF.uniformOfFintype (Left × Right)).bind fun pair => continuation pair.1 pair.2 := by
  ext result
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_fintype, Fintype.sum_prod_type,
    Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [Finset.mul_sum, mul_assoc]

/-- A bind may be rewritten on the support of the sampled law. -/
theorem bind_congr_support {Value Result : Type} {law : PMF Value}
    {first second : Value → PMF Result}
    (agree : ∀ value ∈ law.support, first value = second value) :
    law.bind first = law.bind second := by
  ext result
  simp only [PMF.bind_apply]
  refine tsum_congr fun value => ?_
  by_cases member : value ∈ law.support
  · rw [agree value member]
  · rw [(law.apply_eq_zero_iff value).mpr member, zero_mul, zero_mul]

/-! ### The bridge-key bijection -/

/-- The tape with its bridge key replaced. -/
def setBridge (tape : Garbling.Randomness) (bridgeKey : NonZeroBase) : Garbling.Randomness :=
  { tape with bridgeKey }

/-- Exchanging a tape's bridge key with a separate sample is an involution. -/
def swapBridge : Garbling.Randomness × NonZeroBase ≃ Garbling.Randomness × NonZeroBase where
  toFun pair := (setBridge pair.1 pair.2, pair.1.bridgeKey)
  invFun pair := (setBridge pair.1 pair.2, pair.1.bridgeKey)
  left_inv pair := by
    obtain ⟨tape, _⟩ := pair
    cases tape
    rfl
  right_inv pair := by
    obtain ⟨tape, _⟩ := pair
    cases tape
    rfl

/-- A uniform tape with a fresh uniform bridge key is a uniform tape. -/
theorem uniform_bind_setBridge (continuation : Garbling.Randomness → PMF Bool) :
    ((PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
          continuation (setBridge tape bridgeKey)) =
      (PMF.uniformOfFintype Garbling.Randomness).bind continuation := by
  rw [uniformOfFintype_bind_prod]
  have swapped := uniformOfFintype_bind_equiv swapBridge
    (fun pair : Garbling.Randomness × NonZeroBase => continuation pair.1)
  simp only [swapBridge, Equiv.coe_fn_mk] at swapped
  have unprod : ((PMF.uniformOfFintype (Garbling.Randomness × NonZeroBase)).bind fun pair =>
      continuation pair.1) =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype NonZeroBase).bind fun _ => continuation tape :=
    (uniformOfFintype_bind_prod fun tape (_ : NonZeroBase) => continuation tape).symm
  rw [swapped, unprod]
  simp only [PMF.bind_const]

/-- Multiplication by the scalar is a bijection of the nonzero base field. -/
def mulScalar [FieldCertificate] (scalar : NonZeroScalar) : NonZeroBase ≃ NonZeroBase where
  toFun bridgeKey := ⟨bridgeKey.value * (scalarAsBase scalar).value,
    mul_ne_zero bridgeKey.nonzero (scalarAsBase scalar).nonzero⟩
  invFun carrier := ⟨carrier.value * (scalarAsBase scalar).value⁻¹,
    mul_ne_zero carrier.nonzero (inv_ne_zero (scalarAsBase scalar).nonzero)⟩
  left_inv bridgeKey := by
    cases bridgeKey
    simp only [NonZeroBase.mk.injEq]
    rw [mul_assoc, mul_inv_cancel₀ (scalarAsBase scalar).nonzero, mul_one]
  right_inv carrier := by
    cases carrier
    simp only [NonZeroBase.mk.injEq]
    rw [mul_assoc, inv_mul_cancel₀ (scalarAsBase scalar).nonzero, mul_one]

/-! ### The shared core of both games -/

/-- The state both games project onto: the public oracle view and the label key. -/
abbrev Core := View × InputMacKey

/-- The core handler answers from the view and never changes the state. -/
def coreHandler : OracleHandler (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Core :=
  publicHandler Prod.fst

/-- Both games after their first stage: the adversary chooses an input, receives the
selected labels of the core's key, and decides. -/
def coreGame
    (adversary : AdaptiveAdversary (publicOracleSpec FixedKeyIndex Garbling.EncIndex)
      AffineInput Garbling.Public LamportSignature Unit)
    (parameter : Nat) (auxiliary : Unit) (circuit : Garbling.Public) (core : Core) : PMF Bool :=
  ((adversary.chooseInput parameter circuit auxiliary).run coreHandler core).bind fun selected =>
    PMF.map Prod.fst ((adversary.decide parameter circuit
      (Lamport.selectedLabels (selected.2.2.encodeAffine selected.1.1)) auxiliary
      selected.1.2).run coreHandler selected.2)

/-- A public handler never changes its state. -/
theorem run_publicHandler_support {Tape Result FixedIndex EncIndex : Type}
    (project : Tape → PublicOracle FixedIndex EncIndex) {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget) (tape : Tape)
    (output : Result × Tape)
    (member : output ∈ (program.run (publicHandler project) tape).support) :
    output.2 = tape := by
  induction program generalizing tape with
  | pure distribution =>
    rw [OracleProgram.run_pure, PMF.support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl
  | query request next inductionHypothesis =>
    rw [OracleProgram.run_query] at member
    exact inductionHypothesis _ tape member
  | sample distribution next inductionHypothesis =>
    rw [OracleProgram.run_sample, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨value, _, member⟩ := member
    exact inductionHypothesis value tape member

/-- A game whose handler projects onto the core handler is the core game. -/
theorem bind_run_project {StateOne : Type}
    (handler : OracleHandler (publicOracleSpec FixedKeyIndex Garbling.EncIndex) StateOne)
    (project : StateOne → Core)
    (agree : ∀ query state, (handler query state).1 = (coreHandler query (project state)).1 ∧
      project (handler query state).2 = (coreHandler query (project state)).2)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedKeyIndex Garbling.EncIndex)
      AffineInput Garbling.Public LamportSignature Unit)
    (parameter : Nat) (auxiliary : Unit) (circuit : Garbling.Public) (state : StateOne) :
    (((adversary.chooseInput parameter circuit auxiliary).run handler state).bind fun selected =>
      PMF.map Prod.fst ((adversary.decide parameter circuit
        (Lamport.selectedLabels ((project selected.2).2.encodeAffine selected.1.1)) auxiliary
        selected.1.2).run handler selected.2)) =
      coreGame adversary parameter auxiliary circuit (project state) := by
  have second : ∀ selected : (AffineInput × adversary.State) × StateOne,
      PMF.map Prod.fst ((adversary.decide parameter circuit
        (Lamport.selectedLabels ((project selected.2).2.encodeAffine selected.1.1)) auxiliary
        selected.1.2).run handler selected.2) =
      PMF.map Prod.fst ((adversary.decide parameter circuit
        (Lamport.selectedLabels ((project selected.2).2.encodeAffine selected.1.1)) auxiliary
        selected.1.2).run coreHandler (project selected.2)) := by
    intro selected
    rw [← OracleProgram.run_project handler coreHandler project agree, PMF.map_comp]
    rfl
  rw [funext second, coreGame,
    ← OracleProgram.run_project handler coreHandler project agree
      (adversary.chooseInput parameter circuit auxiliary) state, PMF.bind_map]
  rfl

/-- The core of one tape: its own oracle view and its own label key. -/
def tapeCore (tape : Garbling.Randomness) : Core :=
  (Garbling.evaluationOracle tape, tape.inputMacKey)

/-- The real game is a uniform tape feeding the core game. -/
theorem realGame_eq_core [FieldCertificate] [GroupCertificate]
    (witness : Garbling.Randomness)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedKeyIndex Garbling.EncIndex)
      AffineInput Garbling.Public LamportSignature Unit)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    realGame Garbling.garbledCircuit (realTape witness)
        (publicHandler Garbling.evaluationOracle) adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        coreGame adversary parameter auxiliary
          (curveTable tape, Garbling.maskScalar tape.bridgeKey scalar) (tapeCore tape) := by
  unfold realGame realTape uniformRandomTape
  rw [uniformTape_eq, uniformOfFintype_congr _ garblingRandomnessFintype]
  congr 1
  funext tape
  rw [← bind_run_project (publicHandler Garbling.evaluationOracle) tapeCore
    (fun _ _ => ⟨rfl, rfl⟩)]
  refine bind_congr_support fun selected member => ?_
  have same := run_publicHandler_support Garbling.evaluationOracle _ tape selected member
  subst same
  rfl

/-- The hybrid game is a uniform tape and a uniform carrier feeding the core game. -/
theorem hybridGame_eq_core [FieldCertificate] [GroupCertificate]
    (adversary : AdaptiveAdversary (publicOracleSpec FixedKeyIndex Garbling.EncIndex)
      AffineInput Garbling.Public LamportSignature Unit)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) (hybridSimulator scalar)
        idealOracle adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
        (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
          coreGame adversary parameter auxiliary
            (curveTable (setBridge tape ((mulScalar scalar).symm carrier)),
              carrierBits carrier) (tapeCore tape) := by
  unfold idealGame hybridSimulator
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.pure_bind]
  congr 1
  funext tape
  congr 1
  funext carrier
  exact bind_run_project idealOracle (fun state => (state.view, state.inputMacKey))
    (fun _ _ => ⟨rfl, rfl⟩) adversary parameter auxiliary _ _

/-- The carrier of a bridge key `carrier / scalar` is the masked scalar. -/
theorem maskScalar_symm [FieldCertificate] (scalar : NonZeroScalar) (carrier : NonZeroBase) :
    Garbling.maskScalar ((mulScalar scalar).symm carrier) scalar = carrierBits carrier := by
  conv_rhs => rw [← (mulScalar scalar).apply_symm_apply carrier]
  rfl

/-- Marginal match. The real game is the hybrid game: a uniform bridge key times the
scalar is a uniform nonzero carrier, the curve table is the same function of the
tape, and the ideal handler's log is a projection that the challenge's
`run_project` law removes. -/
theorem realGame_eq_hybridGame [FieldCertificate] [GroupCertificate]
    (witness : Garbling.Randomness)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedKeyIndex Garbling.EncIndex)
      AffineInput Garbling.Public LamportSignature Unit)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    realGame Garbling.garbledCircuit (realTape witness)
        (publicHandler Garbling.evaluationOracle) adversary parameter scalar auxiliary =
      idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) (hybridSimulator scalar)
        idealOracle adversary parameter scalar auxiliary := by
  rw [realGame_eq_core, hybridGame_eq_core]
  refine (uniform_bind_setBridge _).symm.trans (congrArg (PMF.bind _) (funext fun tape => ?_))
  refine (uniformOfFintype_bind_equiv (mulScalar scalar).symm _).symm.trans
    (congrArg (PMF.bind _) (funext fun carrier => ?_))
  exact congrArg (fun bits => coreGame adversary parameter auxiliary
    (curveTable (setBridge tape ((mulScalar scalar).symm carrier)), bits) (tapeCore tape))
    (maskScalar_symm scalar carrier)

/-- Steering invisibility. The hybrid and simulated games sample the same tape and
carrier. They differ only when the adversary queries a fixed-key permutation of
adaptor `x7`, position `0`, at a label point that the simulator programs or that
the hybrid table hides, or when the fiber sample and the carrier law deviate
from uniform. Each event costs at most a small constant per query over `2^128`,
which is below one per query over `2^100`. -/
theorem hybridGame_close_to_idealGame [FieldCertificate] [GroupCertificate]
    (adversary : AdaptiveAdversary (publicOracleSpec FixedKeyIndex Garbling.EncIndex)
      AffineInput Garbling.Public LamportSignature Unit)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit) :
    WorkPerAdvantage 100 (adversaryWork adversary parameter)
      (advantage
        (idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) (hybridSimulator scalar)
          idealOracle adversary parameter scalar auxiliary)
        (idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) simulator
          idealOracle adversary parameter scalar auxiliary)) := by
  sorry

/-- The adaptive-privacy obligation follows from the two lemmas above. -/
theorem adaptivePrivacy [FieldCertificate] [GroupCertificate] (witness : Garbling.Randomness) :
    ConcreteAdaptivePrivacy (Aux := Unit) Garbling.garbledCircuit (fun _ => ciphertextBytes)
      simulator (realTape witness) (publicHandler Garbling.evaluationOracle) idealOracle 100 := by
  intro adversary circuit auxiliary parameter
  rw [realGame_eq_hybridGame]
  exact hybridGame_close_to_idealGame adversary parameter (circuit parameter) (auxiliary parameter)

end

end Kriterion.ArgoMAC.Security
