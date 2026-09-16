/-
This file bridges the simulator's conditional programming to the reference
game's unconditional one. The simulator programs a list of requests one at a
time and skips any request that would change a logged answer
(`programAll` / `programIfFresh`), whereas the reference game programs a
partial request family unconditionally (`programIndices`). When every request
is fresh -- the complement of the bad event of the corresponding hop -- and the
requests sit at distinct indices, the two agree: the simulator's steering
state is the reference game's programmed state at the steering gate's slots.
-/

import Proof.DeferredSteering

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit

/-! ### A request list as a partial programming -/

/-- The partial programming of a list of requests: the first request at each index wins. -/
def programsOfRequests : List ProgramRequest → Programs
  | [] => fun _ => none
  | request :: rest => fun index =>
      if index = request.index then some (request.domain, request.range)
      else programsOfRequests rest index

theorem programsOfRequests_nil (index : FixedKeyIndex) :
    programsOfRequests [] index = none := rfl

theorem programsOfRequests_cons (request : ProgramRequest) (rest : List ProgramRequest)
    (index : FixedKeyIndex) :
    programsOfRequests (request :: rest) index =
      if index = request.index then some (request.domain, request.range)
      else programsOfRequests rest index := rfl

/-- An index no request mentions is unprogrammed. -/
theorem programsOfRequests_of_absent (requests : List ProgramRequest) (index : FixedKeyIndex)
    (absent : ∀ request ∈ requests, request.index ≠ index) :
    programsOfRequests requests index = none := by
  induction requests with
  | nil => rfl
  | cons request rest inductionHypothesis =>
    rw [programsOfRequests_cons, if_neg fun equal =>
      absent request List.mem_cons_self equal.symm,
      inductionHypothesis fun other member => absent other (List.mem_cons_of_mem _ member)]

/-- A programmed index carries the label and the range of its request. -/
theorem programsOfRequests_mem (requests : List ProgramRequest) (index : FixedKeyIndex)
    (label range : Block) (requested : programsOfRequests requests index = some (label, range)) :
    ∃ request ∈ requests, request.index = index ∧ request.domain = label ∧
      request.range = range := by
  induction requests with
  | nil => exact absurd requested (by simp [programsOfRequests_nil])
  | cons request rest inductionHypothesis =>
    rw [programsOfRequests_cons] at requested
    split at requested
    · rename_i same
      exact ⟨request, List.mem_cons_self, same.symm, congrArg Prod.fst (Option.some_inj.mp requested),
        congrArg Prod.snd (Option.some_inj.mp requested)⟩
    · obtain ⟨other, member, index, domain, range⟩ := inductionHypothesis requested
      exact ⟨other, List.mem_cons_of_mem _ member, index, domain, range⟩

/-! ### Freshness reads one index only -/

/-- Freshness of a request depends on the view only at the request's own index. -/
theorem ProgramRequest.fresh_congr (request : ProgramRequest) (log : List Query)
    (first second : PermutationOracle FixedKeyIndex Block)
    (same : first.permutation request.index = second.permutation request.index) :
    request.Fresh log first ↔ request.Fresh log second := by
  unfold ProgramRequest.Fresh
  rw [same]

/-- Programming one index leaves the permutations of the other indices unchanged. -/
theorem programPermutation_of_ne (oracle : PermutationOracle FixedKeyIndex Block)
    (request : ProgramRequest) (index : FixedKeyIndex) (different : index ≠ request.index) :
    (programPermutation oracle request).permutation index = oracle.permutation index := by
  simp only [programPermutation, if_neg different]

/-- Programming the remaining requests on a singly programmed oracle is programming the whole
list at once, when no later request repeats the first index. -/
theorem programIndices_programPermutation (request : ProgramRequest) (rest : List ProgramRequest)
    (oracle : PermutationOracle FixedKeyIndex Block)
    (absent : ∀ other ∈ rest, other.index ≠ request.index) :
    programIndices (programsOfRequests rest) (programPermutation oracle request) =
      programIndices (programsOfRequests (request :: rest)) oracle := by
  have fields : ∀ index,
      (programIndices (programsOfRequests rest) (programPermutation oracle request)).permutation
          index =
        (programIndices (programsOfRequests (request :: rest)) oracle).permutation index := by
    intro index
    by_cases same : index = request.index
    · have absentAt : programsOfRequests rest index = none :=
        programsOfRequests_of_absent rest index fun other member => by
          rw [same]
          exact absent other member
      rw [programIndices_none _ _ index absentAt,
        programIndices_eq_programmed _ oracle index request.domain request.range
          (by rw [programsOfRequests_cons, if_pos same]), same]
      simp [programPermutation, programmed]
    · cases requested : programsOfRequests rest index with
      | none =>
        rw [programIndices_none _ _ index requested,
          programIndices_none _ oracle index
            (by rw [programsOfRequests_cons, if_neg same, requested]),
          programPermutation_of_ne oracle request index same]
      | some pair =>
        obtain ⟨label, range⟩ := pair
        rw [programIndices_eq_programmed _ _ index label range requested,
          programIndices_eq_programmed _ oracle index label range
            (by rw [programsOfRequests_cons, if_neg same, requested]),
          programPermutation_of_ne oracle request index same]
  exact congrArg PermutationOracle.mk (funext fields)

/-! ### The bridge -/

/-- A list of fresh requests at distinct indices is programmed unconditionally: the
simulator's `programAll` is the reference game's `programIndices`. This is the deterministic
half of the freshness hop; the bad event is that one of the requests is not fresh. -/
theorem programAll_eq_programIndices (state : State) (requests : List ProgramRequest)
    (fresh : ∀ request ∈ requests, request.Fresh state.log state.view.1)
    (distinct : requests.Pairwise fun first second => first.index ≠ second.index) :
    programAll state requests =
      { state with
        view := (programIndices (programsOfRequests requests) state.view.1, state.view.2) } := by
  induction requests generalizing state with
  | nil =>
    have identity : programIndices (programsOfRequests []) state.view.1 = state.view.1 :=
      congrArg PermutationOracle.mk (funext fun index =>
        programIndices_none (programsOfRequests []) state.view.1 index
          (programsOfRequests_nil index))
    rw [programAll, List.foldl_nil, identity]
  | cons request rest inductionHypothesis =>
    obtain ⟨absent, restDistinct⟩ := List.pairwise_cons.mp distinct
    have programmedState : programIfFresh state request =
        { state with view := (programPermutation state.view.1 request, state.view.2) } := by
      unfold programIfFresh
      rw [if_pos (fresh request List.mem_cons_self)]
    have restFresh : ∀ other ∈ rest,
        other.Fresh (programIfFresh state request).log (programIfFresh state request).view.1 := by
      intro other member
      rw [programIfFresh_log, programmedState]
      refine (ProgramRequest.fresh_congr other state.log state.view.1 _ ?_).mp
        (fresh other (List.mem_cons_of_mem _ member))
      exact (programPermutation_of_ne state.view.1 request other.index
        (Ne.symm (absent other member))).symm
    rw [programAll_cons, inductionHypothesis (programIfFresh state request) restFresh restDistinct,
      programmedState]
    refine congrArg (fun view => { state with view := view }) ?_
    refine congrArg (fun permutations => (permutations, state.view.2)) ?_
    exact programIndices_programPermutation request rest state.view.1
      fun other member => Ne.symm (absent other member)

/-! ### The steering requests -/

/-- The requests the steering issues at the steering gate: the pad slots of a `true` gate,
the hash slots of a `false` one. -/
def steerRequests (table : CurveMembership.Table) (label : Block) (input : AffineInput)
    (wanted : BaseField) (hash : BitVec 384) : List ProgramRequest :=
  if steeringBit input then
    padRequests label (BitAdaptor.fieldBytes wanted ^^^ (table.x7.get 0).trueRow)
  else hashRequests label hash

/-- Both branches of the steering sample a fiber of the requested value: the `true` branch
ignores it. -/
theorem steerTo_eq_map (state : State) (input : AffineInput) (mac : InputMac)
    (wanted : BaseField) :
    steerTo state input mac wanted =
      (uniformHashFiber wanted).map fun hash =>
        programAll state (steerRequests state.table (mac.x.get 0) input wanted hash) := by
  unfold steerTo steerRequests
  split
  · exact (PMF.map_const (uniformHashFiber wanted)
      (programAll state (padRequests (mac.x.get 0)
        (BitAdaptor.fieldBytes wanted ^^^ (state.table.x7.get 0).trueRow)))).symm
  · rfl

theorem steerRequests_index (table : CurveMembership.Table) (label : Block) (input : AffineInput)
    (wanted : BaseField) (hash : BitVec 384) (request : ProgramRequest)
    (member : request ∈ steerRequests table label input wanted hash) :
    request.index.adaptor = CurveAdaptor.x7 ∧ request.index.position = 0 := by
  unfold steerRequests at member
  split at member <;>
    · simp only [padRequests, hashRequests, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- The steering requests sit at distinct indices. -/
theorem steerRequests_distinct (table : CurveMembership.Table) (label : Block)
    (input : AffineInput) (wanted : BaseField) (hash : BitVec 384) :
    (steerRequests table label input wanted hash).Pairwise
      fun first second => first.index ≠ second.index := by
  unfold steerRequests
  split <;>
    · simp only [padRequests, hashRequests, List.pairwise_cons, List.mem_cons,
        List.not_mem_nil, or_false, List.Pairwise.nil, forall_eq_or_imp, forall_eq,
        false_implies, implies_true, and_true]
      decide

/-- The steering requests are the reference game's steering programs. -/
theorem programsOfRequests_steerRequests (key : InputMacKey) (input : AffineInput)
    (table : CurveMembership.Table) (wanted : BaseField) (hash : BitVec 384) :
    programsOfRequests (steerRequests table (selectedLabel key input .x7 0) input wanted hash) =
      steerPrograms key input wanted hash (tableRow table .x7 0) := by
  funext index
  by_cases steering : index.adaptor = CurveAdaptor.x7 ∧ index.position = 0
  · obtain ⟨adaptor, position, slot⟩ := index
    obtain ⟨rfl, rfl⟩ := steering
    unfold steerRequests
    rw [steeringBit_eq]
    cases bit : inputBits input .x7 0 with
    | false =>
      rw [if_neg Bool.false_ne_true]
      cases slot with
      | hash chunk =>
        rw [steerPrograms_hash, bit, if_neg Bool.false_ne_true]
        fin_cases chunk <;>
          simp only [hashRequests, programsOfRequests_cons, programsOfRequests_nil, slotRange] <;>
          rfl
      | pad chunk =>
        rw [steerPrograms_pad, bit, if_neg Bool.false_ne_true]
        simp only [hashRequests, programsOfRequests_cons, programsOfRequests_nil]
        rfl
    | true =>
      rw [if_pos rfl]
      cases slot with
      | hash chunk =>
        rw [steerPrograms_hash, bit, if_pos rfl]
        simp only [padRequests, programsOfRequests_cons, programsOfRequests_nil]
        rfl
      | pad chunk =>
        rw [steerPrograms_pad, bit, if_pos rfl]
        fin_cases chunk <;>
          simp only [padRequests, programsOfRequests_cons, programsOfRequests_nil, slotRange] <;>
          rfl
  · rw [steerPrograms_other _ _ _ _ _ _ steering]
    refine programsOfRequests_of_absent _ index fun request member equal => steering ?_
    obtain ⟨adaptor, position⟩ := steerRequests_index table (selectedLabel key input .x7 0) input
      wanted hash request member
    exact ⟨equal ▸ adaptor, equal ▸ position⟩

/-- On a good log the steering is the reference game's programming of the steering gate: the
simulator's skip-if-logged programming agrees with the unconditional one. -/
theorem programAll_steerRequests (state : State) (key : InputMacKey) (input : AffineInput)
    (wanted : BaseField) (hash : BitVec 384)
    (fresh : ∀ request ∈ steerRequests state.table (selectedLabel key input .x7 0) input wanted hash,
      request.Fresh state.log state.view.1) :
    programAll state (steerRequests state.table (selectedLabel key input .x7 0) input wanted hash) =
      { state with
        view := (programIndices (steerPrograms key input wanted hash (tableRow state.table .x7 0))
          state.view.1, state.view.2) } := by
  rw [programAll_eq_programIndices state _ fresh
      (steerRequests_distinct state.table (selectedLabel key input .x7 0) input wanted hash),
    programsOfRequests_steerRequests key input state.table wanted hash]

end Kriterion.ArgoMAC.Security
