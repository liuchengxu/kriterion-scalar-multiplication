/-
This file puts both reference-shaped rounds into the two-stage shape the
deferred-sampling transfer law consumes, and identifies the joint law the
transfer law has to compare.

Both rounds read the uniform coordinates through exactly two values: the
released table, which the first stage sees, and the selected outputs of the
chosen input, which only the second stage sees. That is precisely the
`twoStageGame` shape of `Proof/Deferred.lean`, with the released table as the
view and the selected outputs as the hidden part, so the glue is definitional.

The joint law of the two values is a function of the visible coordinates: the
table is `tableOfVisible` of them and the outputs are their own `hash` field.
Off the curve the visible law is uniform whatever the bridge key, so the two
joint laws agree outright. On the curve the steering shift of the selected
output at the steering gate carries the visible law of one bridge key to the
visible law of the shifted one, and it leaves the table alone -- so the joint
law of `(table, shifted outputs)` at one bridge key is the joint law of
`(table, outputs)` at the other.
-/

import Proof.Deferred
import Proof.SimulatedReference

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit

/-! ### The released table as a function of the visible coordinates -/

/-- Two curve-membership tables with equal fields are equal. -/
theorem curveTable_ext (first second : CurveMembership.Table) (c0 : first.c0 = second.c0)
    (c1 : first.c1 = second.c1) (c2 : first.c2 = second.c2) (x3 : first.x3 = second.x3)
    (x5 : first.x5 = second.x5) (x7 : first.x7 = second.x7) (y4 : first.y4 = second.y4)
    (y6 : first.y6 = second.y6) : first = second := by
  obtain ⟨_, _, _, _, _, _, _, _⟩ := first
  obtain ⟨_, _, _, _, _, _, _, _⟩ := second
  simp_all

/-- The table the visible coordinates release: the released row in place of the mask, the
two masked secrets, and one table row per gate. -/
def tableOfVisible (visible : Coordinates) : CurveMembership.Table where
  c0 := visible.mask
  c1 := visible.r1
  c2 := visible.r2
  x3 := Vector.ofFn fun position => ⟨visible.pad .x3 position⟩
  x5 := Vector.ofFn fun position => ⟨visible.pad .x5 position⟩
  x7 := Vector.ofFn fun position => ⟨visible.pad .x7 position⟩
  y4 := Vector.ofFn fun position => ⟨visible.pad .y4 position⟩
  y6 := Vector.ofFn fun position => ⟨visible.pad .y6 position⟩

/-- The visible coordinates determine the released table. -/
theorem tableOfVisible_visibleCoordinates (bridgeKey : BaseField) (key : InputMacKey)
    (input : AffineInput) (raw : Coordinates) :
    tableOfVisible (visibleCoordinates bridgeKey key input raw) = raw.table bridgeKey key := by
  have rows : ∀ adaptor : CurveAdaptor,
      (Vector.ofFn fun position =>
          (⟨(visibleCoordinates bridgeKey key input raw).pad adaptor position⟩ :
            BitAdaptor.Table)) =
        tableRows (raw.table bridgeKey key) adaptor := by
    intro adaptor
    refine Vector.ext fun position member => ?_
    rw [Vector.getElem_ofFn,
      ← Vector.get_eq_getElem (index := ⟨position, member⟩) (tableRows _ adaptor),
      Coordinates.table_rows]
    rfl
  refine curveTable_ext _ _ ?_ ?_ ?_ (rows .x3) (rows .x5) (rows .x7) (rows .y4) (rows .y6)
  · rfl
  · exact (Coordinates.table_c1 bridgeKey key raw).symm
  · exact (Coordinates.table_c2 bridgeKey key raw).symm

/-- The steering shift does not touch the released table: it moves only the selected output
of the steering gate. -/
theorem tableOfVisible_shiftMiddle (shift : BaseField) (visible : Coordinates) :
    tableOfVisible (shiftMiddle shift visible) = tableOfVisible visible := rfl

/-! ### The joint law of the table and the selected outputs -/

/-- The released table and the selected outputs of one input, as a function of the raw
coordinates. This is the pair the deferred comparison compares. -/
def releasedPair (bridgeKey : BaseField) (key : InputMacKey) (input : AffineInput)
    (raw : Coordinates) : CurveMembership.Table × GateValues BaseField :=
  (raw.table bridgeKey key, (encodeCoordinates input raw).hash)

/-- The pair factors through the visible coordinates. -/
theorem releasedPair_eq (bridgeKey : BaseField) (key : InputMacKey) (input : AffineInput)
    (raw : Coordinates) :
    releasedPair bridgeKey key input raw =
      (fun visible : Coordinates => (tableOfVisible visible, visible.hash))
        (visibleCoordinates bridgeKey key input raw) :=
  congrArg (fun table => (table, (encodeCoordinates input raw).hash))
    (tableOfVisible_visibleCoordinates bridgeKey key input raw).symm

noncomputable section

theorem map_releasedPair (bridgeKey : BaseField) (key : InputMacKey) (input : AffineInput) :
    (PMF.uniformOfFintype Coordinates).map (releasedPair bridgeKey key input) =
      ((PMF.uniformOfFintype Coordinates).map
          (visibleCoordinates bridgeKey key input)).map
        fun visible => (tableOfVisible visible, visible.hash) := by
  rw [PMF.map_comp]
  exact congrArg (fun step => PMF.map step (PMF.uniformOfFintype Coordinates))
    (funext fun raw => releasedPair_eq bridgeKey key input raw)

/-- Off the curve the joint law of the released table and the selected outputs does not
depend on the bridge key: the visible law is uniform whatever the bridge key is. -/
theorem map_releasedPair_offCurve [FieldCertificate] (first second : BaseField)
    (key : InputMacKey) (input : AffineInput) (offCurve : curveGap input ≠ 0) :
    (PMF.uniformOfFintype Coordinates).map (releasedPair first key input) =
      (PMF.uniformOfFintype Coordinates).map (releasedPair second key input) := by
  rw [map_releasedPair, map_releasedPair, visibleCoordinates_offCurve first key input offCurve,
    visibleCoordinates_offCurve second key input offCurve]

/-- On the curve, shifting the selected output of the steering gate carries the joint law of
one bridge key to the joint law of the shifted bridge key. The table is untouched, so only
the outputs move. -/
theorem map_releasedPair_onCurve (bridgeKey shift : BaseField) (key : InputMacKey)
    (input : AffineInput) (onCurve : curveGap input = 0) :
    (PMF.uniformOfFintype Coordinates).map (fun raw =>
        ((releasedPair bridgeKey key input raw).1,
          shiftSteering shift (releasedPair bridgeKey key input raw).2)) =
      (PMF.uniformOfFintype Coordinates).map (releasedPair (bridgeKey + shift) key input) := by
  have left : (PMF.uniformOfFintype Coordinates).map (fun raw =>
        ((releasedPair bridgeKey key input raw).1,
          shiftSteering shift (releasedPair bridgeKey key input raw).2)) =
      (((PMF.uniformOfFintype Coordinates).map
          (visibleCoordinates bridgeKey key input)).map (shiftMiddle shift)).map
        fun visible => (tableOfVisible visible, visible.hash) := by
    rw [PMF.map_comp, PMF.map_comp]
    refine congrArg (fun step => PMF.map step (PMF.uniformOfFintype Coordinates))
      (funext fun raw => ?_)
    show ((releasedPair bridgeKey key input raw).1,
        shiftSteering shift (releasedPair bridgeKey key input raw).2) =
      (tableOfVisible (shiftMiddle shift (visibleCoordinates bridgeKey key input raw)),
        (shiftMiddle shift (visibleCoordinates bridgeKey key input raw)).hash)
    rw [releasedPair_eq]
    rfl
  rw [left, visibleCoordinates_onCurve bridgeKey shift key input onCurve, map_releasedPair]

/-! ### Both rounds in two-stage shape -/

/-- The first stage of a reference-shaped round, as a function of the released table. -/
def releasedStageOne (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) (view : View)
    (carrier : NonZeroBase) (table : CurveMembership.Table) :
    PMF ((AffineInput × adversary.State) × List Query) :=
  loggedFirstStage adversary parameter auxiliary (table, carrierBits carrier) view

/-- The reference game's second stage, as a function of the released table, the selected
outputs and the first stage's outcome. -/
def releasedStageTwo (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) (view : View)
    (key : InputMacKey) (carrier : NonZeroBase) (table : CurveMembership.Table)
    (outputs : GateValues BaseField)
    (outcome : (AffineInput × adversary.State) × List Query) : PMF Bool :=
  (uniformHashFibers outputs).bind fun fibers =>
    (selectedStageTwo adversary parameter auxiliary (table, carrierBits carrier) outcome.1.1
      outcome.1.2 outputs fibers (stageTwoState view outcome.2 table carrier key)).map Prod.fst

/-- The steered reference game's second stage, as a function of the released table, the
selected outputs and the first stage's outcome. -/
def steeredReleasedStageTwo [FieldCertificate] [GroupCertificate] (scalar : NonZeroScalar)
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) (view : View)
    (key : InputMacKey) (carrier : NonZeroBase) (table : CurveMembership.Table)
    (outputs : GateValues BaseField)
    (outcome : (AffineInput × adversary.State) × List Query) : PMF Bool :=
  (uniformHashFibers outputs).bind fun fibers =>
    (selectedSimulatedStageTwo adversary parameter auxiliary (table, carrierBits carrier)
      outcome.1.1 (checkedScalarMultiplication scalar.value outcome.1.1) outcome.1.2 outputs
      fibers (stageTwoState view outcome.2 table carrier key)).map Prod.fst

/-- The reference round on uniform coordinates is a two-stage game: the released table is
the view, the selected outputs of the chosen input are the hidden part. -/
theorem referenceRound_eq_twoStageGame (bridge : NonZeroBase → BaseField)
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) (view : View)
    (key : InputMacKey) (carrier : NonZeroBase) :
    ((PMF.uniformOfFintype Coordinates).bind fun raw =>
        referenceRound bridge adversary parameter auxiliary view key carrier raw) =
      twoStageGame (PMF.uniformOfFintype Coordinates)
        (fun raw => raw.table (bridge carrier) key)
        (fun outcome raw => (releasedPair (bridge carrier) key outcome.1.1 raw).2)
        (releasedStageOne adversary parameter auxiliary view carrier)
        (releasedStageTwo adversary parameter auxiliary view key carrier) := rfl

/-- The steered reference round on uniform coordinates is the same two-stage game with the
simulator's second stage. -/
theorem steeredReferenceRound_eq_twoStageGame [FieldCertificate] [GroupCertificate]
    (bridge : NonZeroBase → BaseField) (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (view : View) (key : InputMacKey)
    (carrier : NonZeroBase) :
    ((PMF.uniformOfFintype Coordinates).bind fun raw =>
        steeredReferenceRound bridge scalar adversary parameter auxiliary view key carrier
          raw) =
      twoStageGame (PMF.uniformOfFintype Coordinates)
        (fun raw => raw.table (bridge carrier) key)
        (fun outcome raw => (releasedPair (bridge carrier) key outcome.1.1 raw).2)
        (releasedStageOne adversary parameter auxiliary view carrier)
        (steeredReleasedStageTwo scalar adversary parameter auxiliary view key carrier) := rfl

end

end Kriterion.ArgoMAC.Security
