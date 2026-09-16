/-
This file proves that the second-stage steering is exact: when every program
applies (an empty query log), the steered state's evaluation on the honest
labels releases exactly the requested target. The released value is affine in
the position-`0` digit value of adaptor `x7` with coefficient one, and the
programmed permutations pin that value.
-/

import Proof.Simulator
import Proof.Correctness

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

/-! ### Programming facts -/

theorem programPermutation_self (oracle : PermutationOracle FixedKeyIndex Block)
    (request : ProgramRequest) :
    (programPermutation oracle request).permutation request.index request.domain =
      request.range := by
  simp [programPermutation]

theorem programPermutation_other (oracle : PermutationOracle FixedKeyIndex Block)
    (request : ProgramRequest) (index : FixedKeyIndex) (other : index ≠ request.index) :
    (programPermutation oracle request).permutation index = oracle.permutation index := by
  simp only [programPermutation, if_neg other]

theorem programIfFresh_view_snd (state : State) (request : ProgramRequest) :
    (programIfFresh state request).view.2 = state.view.2 := by
  unfold programIfFresh
  split <;> rfl

theorem programIfFresh_other (state : State) (request : ProgramRequest) (index : FixedKeyIndex)
    (other : index ≠ request.index) :
    (programIfFresh state request).view.1.permutation index =
      state.view.1.permutation index := by
  unfold programIfFresh
  split
  · exact programPermutation_other _ _ _ other
  · rfl

theorem programAll_view_snd (state : State) (requests : List ProgramRequest) :
    (programAll state requests).view.2 = state.view.2 := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest inductionHypothesis =>
    rw [programAll_cons, inductionHypothesis, programIfFresh_view_snd]

/-- Programs at other indices change nothing at this index. -/
theorem programAll_other (state : State) (requests : List ProgramRequest)
    (index : FixedKeyIndex) (other : ∀ request ∈ requests, index ≠ request.index) :
    (programAll state requests).view.1.permutation index =
      state.view.1.permutation index := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest inductionHypothesis =>
    rw [programAll_cons, inductionHypothesis _ (fun r m => other r (List.mem_cons_of_mem _ m)),
      programIfFresh_other _ _ _ (other request List.mem_cons_self)]

/-- With an empty log every program applies. -/
theorem programIfFresh_of_nil (state : State) (empty : state.log = [])
    (request : ProgramRequest) :
    programIfFresh state request =
      { state with view := (programPermutation state.view.1 request, state.view.2) } := by
  unfold programIfFresh
  rw [if_pos]
  simp [ProgramRequest.Fresh, empty]

/-- With an empty log and distinct indices, every requested pair is installed. -/
theorem programAll_self_of_nil (state : State) (empty : state.log = [])
    (requests : List ProgramRequest) (request : ProgramRequest) (member : request ∈ requests)
    (distinct : ∀ other ∈ requests, other.index = request.index → other = request) :
    (programAll state requests).view.1.permutation request.index request.domain =
      request.range := by
  induction requests generalizing state with
  | nil => cases member
  | cons head rest inductionHypothesis =>
    rw [programAll_cons]
    by_cases inRest : request ∈ rest
    · exact inductionHypothesis _ (by rw [programIfFresh_log]; exact empty) inRest
        (fun other m equal => distinct other (List.mem_cons_of_mem _ m) equal)
    · have headEq : head = request := by
        rcases List.mem_cons.mp member with rfl | m
        · rfl
        · exact absurd m inRest
      subst headEq
      rw [programAll_other _ _ _ (fun other m equal => inRest (by
          rw [← distinct other (List.mem_cons_of_mem _ m) equal.symm]; exact m)),
        programIfFresh_of_nil _ empty, programPermutation_self]

theorem steeringIndex_injective : Function.Injective steeringIndex := by
  intro first second equal
  injection equal

/-! ### The steering gate -/

theorem fixedKeyPermutations_steering (oracle : PermutationOracle FixedKeyIndex Block) :
    fixedKeyPermutations oracle .x7 0 = {
      hash := fun slot => oracle.permutation (steeringIndex (.hash slot))
      pad := fun slot => oracle.permutation (steeringIndex (.pad slot)) } := rfl

theorem append_extract_384 (hash : BitVec 384) :
    hash.extractLsb' 256 128 ++ hash.extractLsb' 128 128 ++ hash.extractLsb' 0 128 = hash := by
  ext index bound
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  split
  · rw [Nat.zero_add]
    exact BitVec.getLsbD_eq_getElem bound
  · split
    · rw [show 128 + (index - 128) = index by omega]
      exact BitVec.getLsbD_eq_getElem bound
    · rw [show 256 + (index - 128 - 128) = index by omega]
      exact BitVec.getLsbD_eq_getElem bound

theorem append_extract_256 (pad : BitVec 256) :
    pad.extractLsb' 128 128 ++ pad.extractLsb' 0 128 = pad := by
  ext index bound
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  split
  · rw [Nat.zero_add]
    exact BitVec.getLsbD_eq_getElem bound
  · rw [show 128 + (index - 128) = index by omega]
    exact BitVec.getLsbD_eq_getElem bound

theorem xor_xor_cancel {width : Nat} (value label : BitVec width) :
    (value ^^^ label) ^^^ label = value := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem hashRequests_index (label : Block) (hash : BitVec 384) (request : ProgramRequest)
    (member : request ∈ hashRequests label hash) :
    ∃ slot : FixedKeySlot, request.index = steeringIndex slot := by
  simp only [hashRequests, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem padRequests_index (label : Block) (pad : BitVec 256) (request : ProgramRequest)
    (member : request ∈ padRequests label pad) :
    ∃ slot : FixedKeySlot, request.index = steeringIndex slot := by
  simp only [padRequests, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl <;> exact ⟨_, rfl⟩

theorem hashRequests_distinct (label : Block) (hash : BitVec 384) (request other : ProgramRequest)
    (memberRequest : request ∈ hashRequests label hash) (memberOther : other ∈ hashRequests label hash)
    (equal : other.index = request.index) : other = request := by
  simp only [hashRequests, List.mem_cons, List.mem_nil_iff, or_false] at memberRequest memberOther
  rcases memberRequest with rfl | rfl | rfl <;> rcases memberOther with rfl | rfl | rfl <;>
    first | rfl | exact absurd (steeringIndex_injective equal) (by decide)

theorem padRequests_distinct (label : Block) (pad : BitVec 256) (request other : ProgramRequest)
    (memberRequest : request ∈ padRequests label pad) (memberOther : other ∈ padRequests label pad)
    (equal : other.index = request.index) : other = request := by
  simp only [padRequests, List.mem_cons, List.mem_nil_iff, or_false] at memberRequest memberOther
  rcases memberRequest with rfl | rfl <;> rcases memberOther with rfl | rfl <;>
    first | rfl | exact absurd (steeringIndex_injective equal) (by decide)

/-- Programming the hash slots pins the Davies--Meyer hash of the label. -/
theorem hashToField_programmed (state : State) (empty : state.log = []) (label : Block)
    (hash : BitVec 384) :
    (fixedKeyGate (programAll state (hashRequests label hash)).view.1 .x7 0).hashToField label =
      (hash.toNat : BaseField) := by
  have slot (index : Fin 3) (start : Nat) (member :
      (⟨steeringIndex (.hash index), label, hash.extractLsb' start 128 ^^^ label⟩ : ProgramRequest) ∈
        hashRequests label hash) :
      (programAll state (hashRequests label hash)).view.1.permutation
        (steeringIndex (.hash index)) label = hash.extractLsb' start 128 ^^^ label :=
    programAll_self_of_nil state empty _ _ member
      (fun other m equal => hashRequests_distinct label hash _ other member m equal)
  simp only [fixedKeyGate, BitAdaptor.fixedKeyOracle, BitAdaptor.hashBytes,
    fixedKeyPermutations_steering, daviesMeyer, Cryptography.xor]
  rw [slot 0 0 (by simp [hashRequests]), slot 1 128 (by simp [hashRequests]),
    slot 2 256 (by simp [hashRequests]), xor_xor_cancel, xor_xor_cancel, xor_xor_cancel,
    append_extract_384]

/-- Programming the pad slots pins the Davies--Meyer pad of the label. -/
theorem padBytes_programmed (state : State) (empty : state.log = []) (label : Block)
    (pad : BitVec 256) :
    BitAdaptor.padBytes (fixedKeyPermutations
      (programAll state (padRequests label pad)).view.1 .x7 0) label = pad := by
  have slot (index : Fin 2) (start : Nat) (member :
      (⟨steeringIndex (.pad index), label, pad.extractLsb' start 128 ^^^ label⟩ : ProgramRequest) ∈
        padRequests label pad) :
      (programAll state (padRequests label pad)).view.1.permutation
        (steeringIndex (.pad index)) label = pad.extractLsb' start 128 ^^^ label :=
    programAll_self_of_nil state empty _ _ member
      (fun other m equal => padRequests_distinct label pad _ other member m equal)
  simp only [BitAdaptor.padBytes, fixedKeyPermutations_steering, daviesMeyer, Cryptography.xor]
  rw [slot 0 0 (by simp [padRequests]), slot 1 128 (by simp [padRequests]),
    xor_xor_cancel, xor_xor_cancel, append_extract_256]

/-- Programming the pad slots to the row's mask decrypts the row to `wanted`. -/
theorem decrypt_programmed (state : State) (empty : state.log = []) (label : Block)
    (row : BitAdaptor.Ciphertext) (wanted : BaseField) :
    (fixedKeyGate (programAll state
      (padRequests label (BitAdaptor.fieldBytes wanted ^^^ row))).view.1 .x7 0).decrypt label row =
      wanted := by
  simp only [fixedKeyGate, BitAdaptor.fixedKeyOracle]
  rw [padBytes_programmed state empty, xor_xor_cancel]
  simp only [BitAdaptor.fieldBytes, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (lt_trans wanted.val_lt (by decide))]
  exact ZMod.natCast_zmod_val wanted

/-- Programs at the steering gate leave every other gate unchanged. -/
theorem fixedKeyGate_programAll_other (state : State) (requests : List ProgramRequest)
    (steering : ∀ request ∈ requests, ∃ slot, request.index = steeringIndex slot)
    (adaptor : CurveAdaptor) (position : Nat)
    (other : adaptor ≠ .x7 ∨ position % coordinateBitCount ≠ 0) :
    fixedKeyGate (programAll state requests).view.1 adaptor position =
      fixedKeyGate state.view.1 adaptor position := by
  have untouched (slot : FixedKeySlot) :
      (programAll state requests).view.1.permutation
        { adaptor, position := ⟨position % coordinateBitCount, Nat.mod_lt _ (by decide)⟩, slot } =
      state.view.1.permutation
        { adaptor, position := ⟨position % coordinateBitCount, Nat.mod_lt _ (by decide)⟩, slot } := by
    apply programAll_other
    intro request member equal
    obtain ⟨steeringSlot, index⟩ := steering request member
    rw [index] at equal
    simp only [steeringIndex, FixedKeyIndex.mk.injEq] at equal
    rcases other with different | different
    · exact different equal.1
    · exact different (congrArg Fin.val equal.2.1)
  simp only [fixedKeyGate, fixedKeyPermutations, untouched]

/-- The released value is affine in the steering gate's value with coefficient one. -/
theorem fromBits_shift (first second : Fin coordinateBitCount → BaseField)
    (same : ∀ index, index ≠ 0 → second index = first index) :
    DigitAdaptor.fromBits second = DigitAdaptor.fromBits first + (second 0 - first 0) := by
  unfold DigitAdaptor.fromBits
  conv_lhs => rw [Fin.foldr_succ]
  conv_rhs => rw [Fin.foldr_succ]
  have tails : (fun (index : Fin 253) value => 2 * value + second index.succ) =
      fun index value => 2 * value + first index.succ := by
    funext index value
    rw [same index.succ (Fin.succ_ne_zero index)]
  rw [tails]
  ring

theorem evaluate_shift (oracles oracles' : CurveMembership.Oracles)
    (table : CurveMembership.Table) (input : AffineInput) (mac : InputMac)
    (y4 : oracles'.y4 = oracles.y4) (y6 : oracles'.y6 = oracles.y6)
    (x3 : oracles'.x3 = oracles.x3) (x5 : oracles'.x5 = oracles.x5)
    (x7 : ∀ position < coordinateBitCount, position ≠ 0 →
      oracles'.x7 position = oracles.x7 position) :
    CurveMembership.evaluate oracles' table input mac =
      CurveMembership.evaluate oracles table input mac +
        (BitAdaptor.evaluate (oracles'.x7 0) (table.x7.get 0) (steeringBit input) (mac.x.get 0) -
          BitAdaptor.evaluate (oracles.x7 0) (table.x7.get 0) (steeringBit input)
            (mac.x.get 0)) := by
  have digit : CurveMembership.evaluateDigit oracles'.x7 table.x7 input.x mac.x =
      CurveMembership.evaluateDigit oracles.x7 table.x7 input.x mac.x +
        (BitAdaptor.evaluate (oracles'.x7 0) (table.x7.get 0) (steeringBit input) (mac.x.get 0) -
          BitAdaptor.evaluate (oracles.x7 0) (table.x7.get 0) (steeringBit input)
            (mac.x.get 0)) := by
    simp only [CurveMembership.evaluateDigit, DigitAdaptor.evaluate, Vector.get_ofFn]
    rw [fromBits_shift]
    · rfl
    · intro index nonzero
      rw [x7 index.val index.isLt (fun zero => nonzero (Fin.ext zero))]
  simp only [CurveMembership.evaluate]
  rw [digit, y4, y6, x3, x5]
  ring

/-- With an empty log the steered evaluation releases exactly the target. -/
theorem steer_release (state : State) (input : AffineInput) (mac : InputMac)
    (target : BaseField) (empty : state.log = []) (next : State)
    (member : next ∈ (steer state input mac target).support) :
    CurveMembership.evaluate (curveOracles next.view.1) next.table input mac = target := by
  unfold steer at member
  simp only at member
  have shift (requests : List ProgramRequest)
      (steering : ∀ request ∈ requests, ∃ slot, request.index = steeringIndex slot) :
      CurveMembership.evaluate (curveOracles (programAll state requests).view.1)
          (programAll state requests).table input mac =
        CurveMembership.evaluate (curveOracles state.view.1) state.table input mac +
          (BitAdaptor.evaluate (fixedKeyGate (programAll state requests).view.1 .x7 0)
              (state.table.x7.get 0) (steeringBit input) (mac.x.get 0) -
            BitAdaptor.evaluate (fixedKeyGate state.view.1 .x7 0) (state.table.x7.get 0)
              (steeringBit input) (mac.x.get 0)) := by
    rw [programAll_table]
    apply evaluate_shift
    · funext position
      exact fixedKeyGate_programAll_other state requests steering _ _ (Or.inl (by decide))
    · funext position
      exact fixedKeyGate_programAll_other state requests steering _ _ (Or.inl (by decide))
    · funext position
      exact fixedKeyGate_programAll_other state requests steering _ _ (Or.inl (by decide))
    · funext position
      exact fixedKeyGate_programAll_other state requests steering _ _ (Or.inl (by decide))
    · intro position bound nonzero
      exact fixedKeyGate_programAll_other state requests steering _ _
        (Or.inr (by rw [Nat.mod_eq_of_lt bound]; exact nonzero))
  split at member
  · rename_i bit
    rw [PMF.mem_support_pure_iff] at member
    subst member
    rw [shift _ (padRequests_index _ _)]
    simp only [BitAdaptor.evaluate, bit, if_true]
    rw [decrypt_programmed state empty]
    ring
  · rename_i bit
    have bitFalse : steeringBit input = false := by simpa using bit
    rw [PMF.support_map] at member
    obtain ⟨hash, hashMember, rfl⟩ := member
    have fiber : (hash.toNat : BaseField) =
        BitAdaptor.evaluate (fixedKeyGate state.view.1 .x7 0) (state.table.x7.get 0)
            (steeringBit input) (mac.x.get 0) +
          (target - CurveMembership.evaluate (curveOracles state.view.1) state.table input mac) := by
      unfold uniformHashFiber at hashMember
      rw [PMF.support_map] at hashMember
      obtain ⟨⟨value, property⟩, _, rfl⟩ := hashMember
      exact property
    rw [shift _ (hashRequests_index _ _)]
    simp only [BitAdaptor.evaluate, bitFalse, Bool.false_eq_true, if_false] at fiber ⊢
    rw [hashToField_programmed state empty, fiber]
    ring

/-! ### Evaluate-consistency of the simulated view -/

theorem carrierBits_toNat (carrier : NonZeroBase) :
    (carrierBits carrier).toNat = carrier.value.val := by
  rw [carrierBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans carrier.value.val_lt (by decide))

/-- Dividing the carrier by the steering target returns the scalar. -/
theorem unmaskScalar_target [FieldCertificate] (carrier : NonZeroBase) (scalar : NonZeroScalar) :
    Garbling.unmaskScalar (carrier.value * ((scalar.value.val : Nat) : BaseField)⁻¹)
      (carrierBits carrier) = scalar.value := by
  rw [Garbling.unmaskScalar, carrierBits_toNat, ZMod.natCast_zmod_val, mul_inv, inv_inv,
    ← mul_assoc, mul_inv_cancel₀ carrier.nonzero, one_mul, Garbling.val_scalarCast,
    ZMod.natCast_zmod_val]

theorem decodePoint_ne_zero [FieldCertificate] (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) : point ≠ 0 := by
  unfold decodePoint at decoded
  split at decoded
  · rw [← Option.some_inj.mp decoded]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  · cases decoded

/-- The steering target is nonzero, so the simulated evaluation never fails. -/
theorem steeringTarget_ne_zero [FieldCertificate] (carrier : NonZeroBase) (scalar : NonZeroScalar) :
    carrier.value * ((scalar.value.val : Nat) : BaseField)⁻¹ ≠ 0 :=
  mul_ne_zero carrier.nonzero (inv_ne_zero (scalarAsBase scalar).nonzero)

/-- On an on-curve input with an empty log, the honest evaluator applied to the
simulated public value and the simulated labels returns the target output. This
is the evaluate-consistency the steering exists to provide. -/
theorem simulated_evaluate [FieldCertificate] [GroupCertificate] (state : State)
    (empty : state.log = []) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) (scalar : NonZeroScalar)
    (result : GarbledCircuit.LamportSignature × State)
    (member : result ∈ (simulateEncode state input
      (checkedScalarMultiplication scalar.value input)).support) :
    Garbling.evaluate result.2.view (state.table, carrierBits state.carrier) input result.1 =
      some (checkedScalarMultiplication scalar.value input) := by
  have target : steeringTarget state.carrier input (checkedScalarMultiplication scalar.value input) =
      some (state.carrier.value * ((scalar.value.val : Nat) : BaseField)⁻¹) := by
    simp only [checkedScalarMultiplication, decoded, Option.map_some, scalarMultiplication,
      steeringTarget, discreteLog_smul (decodePoint_ne_zero input point decoded)]
  unfold simulateEncode at member
  simp only [target] at member
  rw [PMF.support_map] at member
  obtain ⟨next, nextMember, rfl⟩ := member
  have released := steer_release state input _ _ empty next nextMember
  obtain ⟨requests, rfl⟩ := steer_support state input _ _ next nextMember
  rw [programAll_table] at released
  simp only [Garbling.evaluate, decoded, Lamport.splitLabels_selectedLabels, released,
    if_neg (steeringTarget_ne_zero state.carrier scalar), unmaskScalar_target,
    checkedScalarMultiplication, Option.map_some, scalarMultiplication]

end Kriterion.ArgoMAC.Security
