/-
This file reads the gate values of the reference game as the independent
coordinates of one function type and instantiates the tensorisation facts on
them: a uniform gate value family is the product of uniform gate laws, the
fiber sample of all gates is the product of the per-gate fiber samples, the
1270 digests of a reference sample differ from 1270 uniform 384-bit strings in
total by at most `1270 * p / 2 ^ 384`, and resampling the steering gate's fiber
is the fiber sample of the outputs with the steering output replaced.
-/

import Proof.Product
import Proof.DeferredSteering

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-! ### Gates as one index -/

/-- One gate: an adaptor family and a coordinate bit position. -/
abbrev Gate := CurveAdaptor × Fin coordinateBitCount

/-- The gate values of one function of gates. -/
def gateCurry (Value : Type) : (Gate → Value) ≃ GateValues Value :=
  Equiv.curry CurveAdaptor (Fin coordinateBitCount) Value

theorem gateCurry_apply (Value : Type) (values : Gate → Value) (adaptor : CurveAdaptor)
    (position : Fin coordinateBitCount) :
    gateCurry Value values adaptor position = values (adaptor, position) := rfl

/-- The law of independent gates. -/
def gateProduct {Value : Type} [Fintype Value] (laws : Gate → PMF Value) :
    PMF (GateValues Value) :=
  (productPMF laws).map (gateCurry Value)

theorem card_curveAdaptor : Fintype.card CurveAdaptor = 5 := rfl

/-- The circuit has 1270 gates: five adaptor families times the coordinate bit positions. -/
theorem card_gate : Fintype.card Gate = 1270 := by
  rw [Fintype.card_prod, Fintype.card_fin, card_curveAdaptor]
  rfl

/-- A uniform gate value family is the product of uniform gate laws. -/
theorem uniformOfFintype_gateValues (Value : Type) [Fintype Value] [Nonempty Value] :
    PMF.uniformOfFintype (GateValues Value) =
      gateProduct fun _ : Gate => PMF.uniformOfFintype Value := by
  rw [gateProduct, ← uniformOfFintype_pi, uniformOfFintype_map_bijection]

/-! ### The fiber samples of all gates -/

/-- The digests of all gates in the fibers of the given outputs, indexed by one gate. -/
abbrev GateFibers (outputs : GateValues BaseField) : Type :=
  { values : Gate → BitVec 384 //
    ∀ gate, ((values gate).toNat : BaseField) = outputs gate.1 gate.2 }

/-- Currying the gate index is a bijection of the fiber families. -/
def gateFibersEquiv (outputs : GateValues BaseField) :
    GateFibers outputs ≃ HashFibers outputs :=
  Equiv.subtypeEquiv (gateCurry (BitVec 384)) fun _values =>
    ⟨fun holds adaptor position => holds (adaptor, position), fun holds gate => holds gate.1 gate.2⟩

instance (outputs : GateValues BaseField) : Nonempty (GateFibers outputs) :=
  (Equiv.nonempty_congr (gateFibersEquiv outputs)).mpr inferInstance

/-- The fiber sample of all gates is the product of the per-gate fiber samples. -/
theorem uniformHashFibers_eq_gateProduct (outputs : GateValues BaseField) :
    uniformHashFibers outputs =
      gateProduct fun gate => uniformHashFiber (outputs gate.1 gate.2) := by
  have base := uniform_subtypePi_map_val (Index := Gate) (Value := BitVec 384)
    fun gate (hash : BitVec 384) => ((hash.toNat : BaseField) = outputs gate.1 gate.2)
  have coordinates : ((PMF.uniformOfFintype (GateFibers outputs)).map Subtype.val) =
      productPMF fun gate => uniformHashFiber (outputs gate.1 gate.2) := base
  have carried : (PMF.uniformOfFintype (HashFibers outputs)) =
      (PMF.uniformOfFintype (GateFibers outputs)).map (gateFibersEquiv outputs) :=
    (uniformOfFintype_map_bijection (gateFibersEquiv outputs)).symm
  have composed : (Subtype.val ∘ ⇑(gateFibersEquiv outputs)) =
      (⇑(gateCurry (BitVec 384)) ∘ Subtype.val) := funext fun _element => rfl
  rw [uniformHashFibers, carried, PMF.map_comp, composed, ← PMF.map_comp, coordinates, gateProduct]

/-! ### The tensorised digest replacement -/

/-- A uniform field element of every gate followed by a uniform fiber sample of every gate
differs from a uniform digest of every gate in total by at most `1270 * p / 2 ^ 384`. -/
theorem hashFibers_total_difference :
    totalDifference ((PMF.uniformOfFintype (GateValues BaseField)).bind uniformHashFibers)
        (PMF.uniformOfFintype (GateValues (BitVec 384))) ≤
      1270 * ((baseFieldModulus : ℝ) / 2 ^ 384) := by
  have mixture : (PMF.uniformOfFintype (GateValues BaseField)).bind uniformHashFibers =
      gateProduct fun _ : Gate => (PMF.uniformOfFintype BaseField).bind uniformHashFiber := by
    rw [uniformOfFintype_gateValues BaseField, gateProduct, PMF.bind_map]
    have inner : ∀ values : Gate → BaseField,
        (uniformHashFibers ∘ gateCurry BaseField) values =
          (productPMF fun gate => uniformHashFiber (values gate)).map (gateCurry (BitVec 384)) := by
      intro values
      exact uniformHashFibers_eq_gateProduct (gateCurry BaseField values)
    rw [funext inner, ← PMF.map_bind, gateProduct,
      productPMF_bind (fun _ : Gate => PMF.uniformOfFintype BaseField)
        fun _ : Gate => uniformHashFiber]
  rw [mixture, uniformOfFintype_gateValues (BitVec 384), gateProduct, gateProduct,
    totalDifference_map_bijection]
  refine (totalDifference_productPMF _ _).trans ?_
  rw [Finset.sum_const, Finset.card_univ, card_gate, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left hashFiber_total_difference (by norm_num)

/-! ### Gates a continuation never reads -/

/-- Replace one gate's value. -/
def setGate {Value : Type} (gate : Gate) (value : Value) (values : GateValues Value) :
    GateValues Value :=
  fun adaptor position => if (adaptor, position) = gate then value else values adaptor position

theorem setGate_apply {Value : Type} (gate : Gate) (value : Value) (values : GateValues Value)
    (adaptor : CurveAdaptor) (position : Fin coordinateBitCount) :
    setGate gate value values adaptor position =
      if (adaptor, position) = gate then value else values adaptor position := rfl

/-- Replacing one gate's value is the coordinate update at that gate. -/
theorem setGate_gateCurry {Value : Type} (gate : Gate) (value : Value) (values : Gate → Value) :
    setGate gate value (gateCurry Value values) =
      gateCurry Value (Function.update values gate value) := by
  funext adaptor position
  simp only [setGate_apply, gateCurry_apply]
  by_cases same : (adaptor, position) = gate
  · rw [if_pos same, same, Function.update_self]
  · rw [if_neg same, Function.update_of_ne same]

/-- Two fiber samples whose outputs agree off a finite set of gates give the same game to a
continuation that never reads those gates' fibers. -/
theorem uniformHashFibers_bind_congr {Outcome : Type} (first second : GateValues BaseField)
    (changed : Finset Gate) (continuation : GateValues (BitVec 384) → PMF Outcome)
    (agree : ∀ gate ∉ changed, first gate.1 gate.2 = second gate.1 gate.2)
    (unread : ∀ gate ∈ changed, ∀ (fibers : GateValues (BitVec 384)) (value : BitVec 384),
      continuation (setGate gate value fibers) = continuation fibers) :
    (uniformHashFibers first).bind continuation =
      (uniformHashFibers second).bind continuation := by
  rw [uniformHashFibers_eq_gateProduct, uniformHashFibers_eq_gateProduct, gateProduct, gateProduct,
    PMF.bind_map, PMF.bind_map]
  refine productPMF_bind_congr _ _ changed (continuation ∘ gateCurry (BitVec 384))
    (fun gate notMember => congrArg uniformHashFiber (agree gate notMember)) ?_
  intro gate member values value
  simp only [Function.comp_def]
  rw [← setGate_gateCurry, unread gate member]

/-! ### Resampling the steering gate -/

/-- The steering gate: adaptor `x7`, bit position `0`. -/
def steeringGate : Gate := (.x7, 0)

theorem gate_ne_steeringGate (gate : Gate)
    (other : ¬(gate.1 = CurveAdaptor.x7 ∧ gate.2 = 0)) : gate ≠ steeringGate := by
  intro equal
  exact other ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩

/-- Replacing the steering gate's value is the coordinate update at the steering gate. -/
theorem setSteering_gateCurry {Value : Type} (value : Value) (values : Gate → Value) :
    setSteering value (gateCurry Value values) =
      gateCurry Value (Function.update values steeringGate value) := by
  funext adaptor position
  by_cases steering : adaptor = CurveAdaptor.x7 ∧ position = 0
  · obtain ⟨rfl, rfl⟩ := steering
    rw [setSteering_steeringGate, gateCurry_apply,
      show ((CurveAdaptor.x7, (0 : Fin coordinateBitCount)) : Gate) = steeringGate from rfl,
      Function.update_self]
  · rw [setSteering_other value _ adaptor position steering, gateCurry_apply, gateCurry_apply,
      Function.update_of_ne (gate_ne_steeringGate (adaptor, position) steering)]

/-- Sampling a fresh fiber for the steering gate is the fiber sample of the outputs with the
steering output replaced. -/
theorem uniformHashFibers_setSteering (outputs : GateValues BaseField) (wanted : BaseField) :
    ((uniformHashFibers outputs).bind fun fibers =>
        (uniformHashFiber wanted).map fun hash => setSteering hash fibers) =
      uniformHashFibers (setSteering wanted outputs) := by
  rw [uniformHashFibers_eq_gateProduct, uniformHashFibers_eq_gateProduct, gateProduct, gateProduct,
    PMF.bind_map]
  have inner : ∀ values : Gate → BitVec 384,
      ((fun fibers => (uniformHashFiber wanted).map fun hash => setSteering hash fibers) ∘
          gateCurry (BitVec 384)) values =
        ((uniformHashFiber wanted).map fun hash =>
          Function.update values steeringGate hash).map (gateCurry (BitVec 384)) := by
    intro values
    rw [PMF.map_comp]
    exact congrArg ((uniformHashFiber wanted).map ·)
      (funext fun hash => setSteering_gateCurry hash values)
  rw [funext inner, ← PMF.map_bind,
    productPMF_bind_update (fun gate => uniformHashFiber (outputs gate.1 gate.2)) steeringGate
      (uniformHashFiber wanted)]
  refine congrArg (PMF.map (gateCurry (BitVec 384))) (congrArg productPMF (funext fun gate => ?_))
  by_cases steering : gate.1 = CurveAdaptor.x7 ∧ gate.2 = 0
  · obtain ⟨first, second⟩ := steering
    rw [show gate = steeringGate from Prod.ext first second, Function.update_self]
    exact congrArg uniformHashFiber (setSteering_steeringGate wanted outputs).symm
  · rw [Function.update_of_ne (gate_ne_steeringGate gate steering),
      setSteering_other wanted outputs gate.1 gate.2 steering]

/-- The steering shift replaces the steering output. -/
theorem shiftSteering_eq_setSteering (shift : BaseField) (outputs : GateValues BaseField) :
    shiftSteering shift outputs = setSteering (outputs .x7 0 + shift) outputs := by
  funext adaptor position
  by_cases steering : adaptor = CurveAdaptor.x7 ∧ position = 0
  · obtain ⟨rfl, rfl⟩ := steering
    rw [setSteering_steeringGate]
    simp [shiftSteering]
  · rw [shiftSteering_other shift outputs adaptor position steering,
      setSteering_other _ outputs adaptor position steering]

end

end Kriterion.ArgoMAC.Security
