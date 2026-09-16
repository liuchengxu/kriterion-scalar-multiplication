/-
This file defines the privacy simulator and its programmable ideal oracle.

The simulator state carries the complete public oracle view, the log of every
adversary query, the public curve table, the carrier, and the label key. The
ideal handler answers from the view and appends the query to the log; it never
changes the view. The first stage garbles a real curve table on a fresh uniform
tape (the table is scalar-free) and publishes a uniform nonzero carrier. The
second stage returns the honest labels; on an on-curve input it recovers the
scalar from the output point and steers the released value to `carrier / scalar`
by programming the fixed-key permutations at the selected label of adaptor `x7`,
bit position `0`. Every program step is skipped when it would change a logged
answer, so every prior answer is preserved.
-/

import Proof.Finite
import Security.AdaptivePrivacy

deriving instance DecidableEq for Kriterion.Cryptography.PublicQuery

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit

instance : Fact (Nat.Prime scalarFieldModulus) := ⟨scalarFieldPrime⟩

instance : Fact (1 < baseFieldModulus) := ⟨by decide⟩

/-- A nonempty tape witness: identity permutations and constant labels. -/
def witnessTape : Garbling.Randomness where
  bridgeKey := ⟨1, one_ne_zero⟩
  curveMask := ⟨1, one_ne_zero⟩
  curveR1 := 0
  curveR2 := 0
  fixedKeyOracle := ⟨fun _ => Equiv.refl Block⟩
  inputMacKey := ⟨Vector.replicate coordinateBitCount ⟨0, 1⟩,
    Vector.replicate coordinateBitCount ⟨0, 1⟩⟩
  encOracle := ⟨fun _ => Equiv.refl Block⟩
  hashOracle := fun _ => (0, 0)

instance : Nonempty Garbling.Randomness := ⟨witnessTape⟩

instance : Nonempty NonZeroBase := ⟨⟨1, one_ne_zero⟩⟩

abbrev Query := PublicQuery FixedKeyIndex Garbling.EncIndex
abbrev View := PublicOracle FixedKeyIndex Garbling.EncIndex

/-- The simulator state: the oracle view, the query log, and the public sample. -/
structure State where
  view : View
  log : List Query
  table : CurveMembership.Table
  carrier : NonZeroBase
  inputMacKey : InputMacKey

/-- The challenge checks the ideal answers against this view. -/
def idealView (state : State) : View := state.view

/-- The ideal handler answers from the view and records the query. -/
def idealOracle : OracleHandler (publicOracleSpec FixedKeyIndex Garbling.EncIndex) State :=
  fun query state => (publicAnswer state.view query, { state with log := query :: state.log })

/-- The scalar-free curve table of one tape. -/
def curveTable (tape : Garbling.Randomness) : CurveMembership.Table :=
  CurveMembership.garble tape.bridgeKey.value tape.curveMask.value tape.curveR1 tape.curveR2
    (curveOracles tape.fixedKeyOracle) tape.inputMacKey

theorem garble_fst (parameter : Nat) (scalar : NonZeroScalar) (tape : Garbling.Randomness) :
    (Garbling.garble parameter scalar tape).1 =
      (curveTable tape, Garbling.maskScalar tape.bridgeKey scalar) := rfl

/-- The carrier's 32-byte form. -/
def carrierBits (carrier : NonZeroBase) : BitVec 256 := BitVec.ofNat 256 carrier.value.val

/-- The first-stage state: the tape's own oracle tables, an empty log, and the sample. -/
def initialState (tape : Garbling.Randomness) (table : CurveMembership.Table)
    (carrier : NonZeroBase) : State where
  view := Garbling.evaluationOracle tape
  log := []
  table := table
  carrier := carrier
  inputMacKey := tape.inputMacKey

/-! ### Permutation programming -/

/-- One requested forward pair of one fixed-key permutation. -/
structure ProgramRequest where
  index : FixedKeyIndex
  domain : Block
  range : Block

/-- Compose the permutation at `index` with a transposition so that `domain ↦ range`.
The old image of `domain` moves to the old preimage of `range`. -/
def programPermutation (oracle : PermutationOracle FixedKeyIndex Block)
    (request : ProgramRequest) : PermutationOracle FixedKeyIndex Block where
  permutation index :=
    if index = request.index then
      (oracle.permutation request.index).trans
        (Equiv.swap (oracle.permutation request.index request.domain) request.range)
    else oracle.permutation index

/-- A program is fresh when none of the four answers it changes has been logged. -/
def ProgramRequest.Fresh (log : List Query) (oracle : PermutationOracle FixedKeyIndex Block)
    (request : ProgramRequest) : Prop :=
  PublicQuery.fixedForward request.index request.domain ∉ log ∧
  PublicQuery.fixedForward request.index
    ((oracle.permutation request.index).symm request.range) ∉ log ∧
  PublicQuery.fixedInverse request.index request.range ∉ log ∧
  PublicQuery.fixedInverse request.index
    (oracle.permutation request.index request.domain) ∉ log

instance (log : List Query) (oracle : PermutationOracle FixedKeyIndex Block)
    (request : ProgramRequest) : Decidable (request.Fresh log oracle) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Program one pair when it is fresh; otherwise leave the state unchanged. -/
def programIfFresh (state : State) (request : ProgramRequest) : State :=
  if request.Fresh state.log state.view.1 then
    { state with view := (programPermutation state.view.1 request, state.view.2) }
  else state

/-- Program a list of pairs in order. -/
def programAll (state : State) (requests : List ProgramRequest) : State :=
  requests.foldl programIfFresh state

theorem programAll_cons (state : State) (request : ProgramRequest)
    (rest : List ProgramRequest) :
    programAll state (request :: rest) = programAll (programIfFresh state request) rest := rfl

theorem programIfFresh_log (state : State) (request : ProgramRequest) :
    (programIfFresh state request).log = state.log := by
  unfold programIfFresh
  split <;> rfl

theorem programIfFresh_table (state : State) (request : ProgramRequest) :
    (programIfFresh state request).table = state.table := by
  unfold programIfFresh
  split <;> rfl

theorem programIfFresh_carrier (state : State) (request : ProgramRequest) :
    (programIfFresh state request).carrier = state.carrier := by
  unfold programIfFresh
  split <;> rfl

theorem programIfFresh_inputMacKey (state : State) (request : ProgramRequest) :
    (programIfFresh state request).inputMacKey = state.inputMacKey := by
  unfold programIfFresh
  split <;> rfl

/-- A fresh program changes no logged answer. -/
theorem programIfFresh_answer (state : State) (request : ProgramRequest) (query : Query)
    (seen : query ∈ state.log) :
    publicAnswer (programIfFresh state request).view query =
      publicAnswer state.view query := by
  unfold programIfFresh
  split
  · rename_i fresh
    obtain ⟨domainUnseen, preimageUnseen, rangeUnseen, imageUnseen⟩ := fresh
    cases query with
    | fixedForward index input =>
      simp only [publicAnswer, programPermutation]
      by_cases same : index = request.index
      · subst same
        rw [if_pos rfl, Equiv.trans_apply]
        refine Equiv.swap_apply_of_ne_of_ne (α := Block) ?_ ?_
        · intro equal
          exact domainUnseen
            (by rw [← (state.view.1.permutation request.index).injective equal]; exact seen)
        · intro equal
          exact preimageUnseen
            (by rw [(Equiv.symm_apply_eq _).mpr equal.symm]; exact seen)
      · rw [if_neg same]
    | fixedInverse index output =>
      simp only [publicAnswer, programPermutation]
      by_cases same : index = request.index
      · subst same
        rw [if_pos rfl, Equiv.symm_trans_apply, Equiv.symm_swap]
        congr 1
        refine Equiv.swap_apply_of_ne_of_ne (α := Block) ?_ ?_
        · intro equal
          exact imageUnseen (by rw [← equal]; exact seen)
        · intro equal
          exact rangeUnseen (by rw [← equal]; exact seen)
      · rw [if_neg same]
    | encForward index input => rfl
    | encInverse index output => rfl
    | hash input => rfl
  · rfl

theorem programAll_log (state : State) (requests : List ProgramRequest) :
    (programAll state requests).log = state.log := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest inductionHypothesis =>
    rw [programAll_cons, inductionHypothesis, programIfFresh_log]

theorem programAll_table (state : State) (requests : List ProgramRequest) :
    (programAll state requests).table = state.table := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest inductionHypothesis =>
    rw [programAll_cons, inductionHypothesis, programIfFresh_table]

theorem programAll_carrier (state : State) (requests : List ProgramRequest) :
    (programAll state requests).carrier = state.carrier := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest inductionHypothesis =>
    rw [programAll_cons, inductionHypothesis, programIfFresh_carrier]

theorem programAll_inputMacKey (state : State) (requests : List ProgramRequest) :
    (programAll state requests).inputMacKey = state.inputMacKey := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest inductionHypothesis =>
    rw [programAll_cons, inductionHypothesis, programIfFresh_inputMacKey]

/-- A sequence of fresh programs changes no logged answer. -/
theorem programAll_answer (state : State) (requests : List ProgramRequest) (query : Query)
    (seen : query ∈ state.log) :
    publicAnswer (programAll state requests).view query = publicAnswer state.view query := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest inductionHypothesis =>
    rw [programAll_cons, inductionHypothesis (programIfFresh state request)
      (by rw [programIfFresh_log]; exact seen), programIfFresh_answer state request query seen]

/-! ### Steering -/

/-- The steering gate: adaptor `x7`, bit position `0`. Its digit enters the released
value with coefficient one. -/
def steeringIndex (slot : FixedKeySlot) : FixedKeyIndex :=
  { adaptor := .x7, position := 0, slot }

/-- The evaluator reads the x-coordinate bit at position `0` to select a label. -/
def steeringBit (input : AffineInput) : Bool :=
  (coordinateBits input.x).getLsb 0

/-- Program the three hash permutations so that the Davies--Meyer hash of `label`
equals `hash`. -/
def hashRequests (label : Block) (hash : BitVec 384) : List ProgramRequest :=
  [ ⟨steeringIndex (.hash 0), label, hash.extractLsb' 0 128 ^^^ label⟩,
    ⟨steeringIndex (.hash 1), label, hash.extractLsb' 128 128 ^^^ label⟩,
    ⟨steeringIndex (.hash 2), label, hash.extractLsb' 256 128 ^^^ label⟩ ]

/-- Program the two pad permutations so that the Davies--Meyer pad of `label`
equals `pad`. -/
def padRequests (label : Block) (pad : BitVec 256) : List ProgramRequest :=
  [ ⟨steeringIndex (.pad 0), label, pad.extractLsb' 0 128 ^^^ label⟩,
    ⟨steeringIndex (.pad 1), label, pad.extractLsb' 128 128 ^^^ label⟩ ]

noncomputable section

set_option exponentiation.threshold 400 in
instance : Fintype (BitVec 384) :=
  Fintype.ofEquiv (Fin (2 ^ 384)) BitVec.equivFin.symm.toEquiv

/-- The 384-bit strings whose field reduction is `target`. -/
abbrev HashFiber (target : BaseField) : Type :=
  { hash : BitVec 384 // (hash.toNat : BaseField) = target }

set_option exponentiation.threshold 400 in
instance (target : BaseField) : Nonempty (HashFiber target) :=
  ⟨⟨BitVec.ofNat 384 target.val, by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans target.val_lt (by decide)),
      ZMod.natCast_zmod_val]⟩⟩

instance (target : BaseField) : Fintype (HashFiber target) :=
  Subtype.fintype _

/-- A uniform 384-bit string in the fiber of `target`. The real hash is uniform on
384 bits, so the simulated hash must not be the canonical short encoding. -/
def uniformHashFiber (target : BaseField) : PMF (BitVec 384) :=
  (PMF.uniformOfFintype (HashFiber target)).map Subtype.val

/-- The scalar that carries `point` to `result`, when one exists. -/
def discreteLog [FieldCertificate] [GroupCertificate] (point result : Point) : ScalarField :=
  if found : ∃ scalar : ScalarField, scalar • point = result then Classical.choose found
  else 0

/-- The scalar is unique on a nonzero point of prime order. -/
theorem smul_left_injective_of_ne_zero [FieldCertificate] [GroupCertificate]
    {point : Point} (nonzero : point ≠ 0) {first second : ScalarField}
    (equal : first • point = second • point) : first = second := by
  have zero : (first - second) • point = 0 := by rw [sub_smul, equal, sub_self]
  rcases smul_eq_zero.mp zero with difference | contradiction
  · exact sub_eq_zero.mp difference
  · exact absurd contradiction nonzero

theorem discreteLog_smul [FieldCertificate] [GroupCertificate] {point : Point}
    (nonzero : point ≠ 0) (scalar : ScalarField) :
    discreteLog point (scalar • point) = scalar := by
  unfold discreteLog
  rw [dif_pos ⟨scalar, rfl⟩]
  exact smul_left_injective_of_ne_zero nonzero (Classical.choose_spec (⟨scalar, rfl⟩ :
    ∃ candidate : ScalarField, candidate • point = scalar • point))

/-- The nonzero scalar as a nonzero base-field element. -/
def scalarAsBase (scalar : NonZeroScalar) : NonZeroBase where
  value := (scalar.value.val : BaseField)
  nonzero := by
    intro zero
    rw [ZMod.natCast_eq_zero_iff] at zero
    have small : scalar.value.val < baseFieldModulus :=
      lt_trans scalar.value.val_lt (by decide)
    exact scalar.nonzero (by
      rw [← ZMod.natCast_zmod_val scalar.value, Nat.eq_zero_of_dvd_of_lt zero small]
      rfl)

/-- The value the steered evaluation must release: `carrier / scalar`, so that the
evaluator's division returns the scalar. Off-curve inputs need no steering. -/
def steeringTarget [FieldCertificate] [GroupCertificate] (carrier : NonZeroBase)
    (input : AffineInput) (output : Option Point) : Option BaseField :=
  match decodePoint input, output with
  | some point, some result =>
    some (carrier.value * ((discreteLog point result).val : BaseField)⁻¹)
  | _, _ => none

/-- Steer the released value to `target`. The current release and the current
position-`0` value of adaptor `x7` are read from the view; the position value is
shifted by the required difference. A `true` bit reads the pad of the selected
label, whose exclusive-or with the table row must be the canonical field bytes. A
`false` bit reads the hash of the selected label, which is uniform in its fiber. -/
def steer (state : State) (input : AffineInput) (mac : InputMac) (target : BaseField) :
    PMF State :=
  let bit := steeringBit input
  let label := mac.x.get 0
  let row := state.table.x7.get 0
  let current := CurveMembership.evaluate (curveOracles state.view.1) state.table input mac
  let position := BitAdaptor.evaluate (fixedKeyGate state.view.1 .x7 0) row bit label
  let wanted := position + (target - current)
  if bit then
    PMF.pure (programAll state (padRequests label (BitAdaptor.fieldBytes wanted ^^^ row.trueRow)))
  else
    (uniformHashFiber wanted).map fun hash => programAll state (hashRequests label hash)

/-- The first stage learns only the parameter and the byte count. -/
def simulateGarble (_parameter _bytes : Nat) : PMF (Garbling.Public × State) :=
  (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
    (PMF.uniformOfFintype NonZeroBase).map fun carrier =>
      ((curveTable tape, carrierBits carrier), initialState tape (curveTable tape) carrier)

/-- The second stage returns the honest labels and steers on-curve inputs. -/
def simulateEncode [FieldCertificate] [GroupCertificate] (state : State) (input : AffineInput)
    (output : Option Point) : PMF (LamportSignature × State) :=
  let mac := state.inputMacKey.encodeAffine input
  let labels := Lamport.selectedLabels mac
  match steeringTarget state.carrier input output with
  | none => PMF.pure (labels, state)
  | some target => (steer state input mac target).map fun next => (labels, next)

/-- The privacy simulator. -/
def simulator [FieldCertificate] [GroupCertificate] :
    Simulator AffineInput (Option Point) Garbling.Public LamportSignature Nat State where
  simulateGarble := simulateGarble
  simulateEncode := simulateEncode

/-- Every steered state is a programmed copy of the input state. -/
theorem steer_support (state : State) (input : AffineInput) (mac : InputMac)
    (target : BaseField) (result : State) (member : result ∈ (steer state input mac target).support) :
    ∃ requests, result = programAll state requests := by
  unfold steer at member
  simp only at member
  split at member
  · exact ⟨_, (PMF.mem_support_pure_iff _ _).mp member⟩
  · rw [PMF.support_map] at member
    obtain ⟨hash, _, rfl⟩ := member
    exact ⟨_, rfl⟩

theorem simulateEncode_support [FieldCertificate] [GroupCertificate] (state : State)
    (input : AffineInput) (output : Option Point) (result : LamportSignature × State)
    (member : result ∈ (simulateEncode state input output).support) :
    ∃ requests, result.2 = programAll state requests := by
  unfold simulateEncode at member
  simp only at member
  split at member
  · rw [(PMF.mem_support_pure_iff _ _).mp member]
    exact ⟨[], rfl⟩
  · rw [PMF.support_map] at member
    obtain ⟨next, nextMember, rfl⟩ := member
    exact steer_support state input _ _ next nextMember

/-- The simulator satisfies the challenge's oracle-state obligations: answers come
from the view, queries never change the view, and every logged answer survives
the second stage. -/
theorem oracleSimulation [FieldCertificate] [GroupCertificate] :
    OracleSimulation simulator idealOracle idealView := by
  refine ⟨fun _ => True, fun state query => query ∈ state.log, fun _ _ _ _ => trivial, ?_, ?_⟩
  · intro query state _
    exact ⟨rfl, rfl, trivial, List.mem_cons_self, fun prior seen => List.mem_cons_of_mem _ seen⟩
  · intro state input output result _ member
    obtain ⟨requests, programmed⟩ := simulateEncode_support state input output result member
    refine ⟨trivial, fun query seen => ?_⟩
    rw [programmed]
    exact ⟨show query ∈ (programAll state requests).log by rw [programAll_log]; exact seen,
      programAll_answer state requests query seen⟩

end

end Kriterion.ArgoMAC.Security
