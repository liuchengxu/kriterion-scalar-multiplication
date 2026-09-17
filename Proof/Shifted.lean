/-
This file performs the *transfer* half of the steering hop: the second of the
two steps of step 7, and the one that must run last.

The steering hop compares the reference game of the hybrid side's bridge key
`c / s` with the steered reference game of the tape's own bridge key `u`. The
route is charge first, transfer second. The charge replaces the steered second
stage -- honest fibers, honest programming, then the steering's second fiber
sample and second programming -- by *one* fiber sample at the **shifted**
outputs and *one* programming, at the cost of the hop's bad event. The game
that results is the `shiftedReferenceRound` of this file: literally the
reference round, except that the hidden part handed to the second stage is the
selected outputs with the steering gate's output shifted by `c / s - u` on the
curve, and unshifted off it.

This file proves the transfer: that game **is** the reference game of `c / s`,
exactly, for every bridge key `u`. Both rounds are the same two-stage game with
the same first stage and the *same* second stage, so the deferred-sampling
transfer law applies with no support side condition: off the curve the joint law
of the released table and the selected outputs does not depend on the bridge key
at all, and on the curve the shift of the steering gate's output carries the
joint law of `u` to the joint law of `u + (c / s - u) = c / s`.

The order matters. Doing the transfer first would require the two second stages
to agree, and they differ exactly at the four points the charge pays for; the
charge must therefore come first, and this file is what it charges *towards*.
-/

import Proof.VisibleGame
import Proof.Assembly

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

noncomputable section

/-! ### The shifted reference round -/

/-- The hidden part of the shifted reference round: the selected outputs of the chosen
input, with the steering gate's output moved to the value the steering would have forced.

On the curve the reference view releases the round's own bridge key, so the steering asks
the steering gate for its selected output shifted by the difference of the two bridge keys.
Off the curve the steering is absent and the outputs are untouched. -/
def shiftedOutputs [FieldCertificate] (scalar : NonZeroScalar)
    (bridge : NonZeroBase → BaseField) (carrier : NonZeroBase) (input : AffineInput)
    (outputs : GateValues BaseField) : GateValues BaseField :=
  if curveGap input = 0 then
    shiftSteering (hybridBridge scalar carrier - bridge carrier) outputs
  else outputs

/-- One round of the shifted reference game: the reference round of `bridge`, except that
the second stage receives the shifted selected outputs. This is the game the steering hop
charges towards -- one fiber sample, at the shifted outputs, and one programming. -/
def shiftedReferenceRound [FieldCertificate] (bridge : NonZeroBase → BaseField)
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (view : View) (key : InputMacKey) (carrier : NonZeroBase) (raw : Coordinates) : PMF Bool :=
  (loggedFirstStage adversary parameter auxiliary
      (raw.table (bridge carrier) key, carrierBits carrier) view).bind fun outcome =>
    releasedStageTwo adversary parameter auxiliary view key carrier
      (raw.table (bridge carrier) key)
      (shiftedOutputs scalar bridge carrier outcome.1.1 (encodeCoordinates outcome.1.1 raw).hash)
      outcome

/-- The shifted reference round on uniform coordinates is the same two-stage game as the
reference round, with the shifted selected outputs as the hidden part. -/
theorem shiftedReferenceRound_eq_twoStageGame [FieldCertificate]
    (bridge : NonZeroBase → BaseField) (scalar : NonZeroScalar) (adversary : Adversary)
    (parameter : Nat) (auxiliary : Unit) (view : View) (key : InputMacKey)
    (carrier : NonZeroBase) :
    ((PMF.uniformOfFintype Coordinates).bind fun raw =>
        shiftedReferenceRound bridge scalar adversary parameter auxiliary view key carrier raw) =
      twoStageGame (PMF.uniformOfFintype Coordinates)
        (fun raw => raw.table (bridge carrier) key)
        (fun outcome raw => shiftedOutputs scalar bridge carrier outcome.1.1
          (releasedPair (bridge carrier) key outcome.1.1 raw).2)
        (releasedStageOne adversary parameter auxiliary view carrier)
        (releasedStageTwo adversary parameter auxiliary view key carrier) := rfl

/-! ### The transfer -/

/-- The joint law of the released table and the shifted selected outputs at bridge key `u`
is the joint law of the released table and the selected outputs at bridge key `c / s`.

Off the curve neither side depends on the bridge key; on the curve the shift of the
steering gate's output is exactly the change of bridge key, because the released row is
affine in the steering gate's selected output with coefficient one. -/
theorem map_shiftedOutputs [FieldCertificate] (scalar : NonZeroScalar) (bridgeKey : BaseField)
    (key : InputMacKey) (carrier : NonZeroBase) (input : AffineInput) :
    (PMF.uniformOfFintype Coordinates).map (fun raw =>
        (raw.table bridgeKey key,
          shiftedOutputs scalar (fun _ => bridgeKey) carrier input
            (releasedPair bridgeKey key input raw).2)) =
      (PMF.uniformOfFintype Coordinates).map (fun raw =>
        (raw.table (hybridBridge scalar carrier) key,
          (releasedPair (hybridBridge scalar carrier) key input raw).2)) := by
  have right : (fun raw : Coordinates =>
      (raw.table (hybridBridge scalar carrier) key,
        (releasedPair (hybridBridge scalar carrier) key input raw).2)) =
      releasedPair (hybridBridge scalar carrier) key input := rfl
  rw [right]
  by_cases onCurve : curveGap input = 0
  · have left : (fun raw : Coordinates =>
        (raw.table bridgeKey key,
          shiftedOutputs scalar (fun _ => bridgeKey) carrier input
            (releasedPair bridgeKey key input raw).2)) =
        fun raw : Coordinates => ((releasedPair bridgeKey key input raw).1,
          shiftSteering (hybridBridge scalar carrier - bridgeKey)
            (releasedPair bridgeKey key input raw).2) := by
      funext raw
      show (raw.table bridgeKey key,
          shiftedOutputs scalar (fun _ => bridgeKey) carrier input
            (releasedPair bridgeKey key input raw).2) = _
      rw [shiftedOutputs, if_pos onCurve]
      rfl
    rw [left, map_releasedPair_onCurve bridgeKey (hybridBridge scalar carrier - bridgeKey) key
      input onCurve, add_sub_cancel]
  · have left : (fun raw : Coordinates =>
        (raw.table bridgeKey key,
          shiftedOutputs scalar (fun _ => bridgeKey) carrier input
            (releasedPair bridgeKey key input raw).2)) =
        releasedPair bridgeKey key input := by
      funext raw
      show (raw.table bridgeKey key,
          shiftedOutputs scalar (fun _ => bridgeKey) carrier input
            (releasedPair bridgeKey key input raw).2) = _
      rw [shiftedOutputs, if_neg onCurve]
      rfl
    rw [left, map_releasedPair_offCurve bridgeKey (hybridBridge scalar carrier) key input onCurve]

/-- The shifted reference round of any bridge key is the reference round of `c / s`. -/
theorem shiftedReferenceRound_eq_referenceRound [FieldCertificate] (scalar : NonZeroScalar)
    (bridgeKey : BaseField) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit)
    (view : View) (key : InputMacKey) (carrier : NonZeroBase) :
    ((PMF.uniformOfFintype Coordinates).bind fun raw =>
        shiftedReferenceRound (fun _ => bridgeKey) scalar adversary parameter auxiliary view key
          carrier raw) =
      (PMF.uniformOfFintype Coordinates).bind fun raw =>
        referenceRound (hybridBridge scalar) adversary parameter auxiliary view key carrier raw := by
  rw [shiftedReferenceRound_eq_twoStageGame, referenceRound_eq_twoStageGame]
  exact twoStageGame_congr _ _ _ _ _ _ _ _ fun outcome =>
    map_shiftedOutputs scalar bridgeKey key carrier outcome.1.1

/-! ### The shifted reference game -/

/-- The shifted reference game: the reference game of `bridge`, except that the second
stage receives the shifted selected outputs. It is written in the split sample shape the
steered reference game uses, so the charge can compare the two rounds under one sample. -/
def shiftedReferenceGame [FieldCertificate] (bridge : NonZeroBase → BaseField)
    (scalar : NonZeroScalar) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    PMF Bool :=
  (PMF.uniformOfFintype Garbling.Randomness).bind fun tape =>
    (PMF.uniformOfFintype InputMacKey).bind fun key =>
      (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype NonZeroBase).bind fun carrier =>
          (PMF.uniformOfFintype Coordinates).bind fun raw =>
            shiftedReferenceRound bridge scalar adversary parameter auxiliary
              (oracle, tape.encOracle, tape.hashOracle) key carrier raw

/-- The transfer, at the level of games: the shifted reference game of any fixed bridge key
is the reference game of the hybrid side's bridge key `c / s`. -/
theorem shiftedReferenceGame_eq_referenceGame [FieldCertificate] (scalar : NonZeroScalar)
    (bridgeKey : BaseField) (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    shiftedReferenceGame (fun _ => bridgeKey) scalar adversary parameter auxiliary =
      referenceGame (hybridBridge scalar) adversary parameter auxiliary := by
  rw [referenceGame_eq_split]
  unfold shiftedReferenceGame
  refine congrArg (PMF.bind _) (funext fun tape => ?_)
  refine congrArg (PMF.bind _) (funext fun key => ?_)
  refine congrArg (PMF.bind _) (funext fun oracle => ?_)
  refine congrArg (PMF.bind _) (funext fun carrier => ?_)
  exact shiftedReferenceRound_eq_referenceRound scalar bridgeKey adversary parameter auxiliary
    (oracle, tape.encOracle, tape.hashOracle) key carrier

/-- The transfer with the bridge key sampled, in the shape the chain consumes. -/
theorem bind_shiftedReferenceGame_eq_referenceGame [FieldCertificate] (scalar : NonZeroScalar)
    (adversary : Adversary) (parameter : Nat) (auxiliary : Unit) :
    ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        shiftedReferenceGame (fun _ => bridgeKey.value) scalar adversary parameter auxiliary) =
      referenceGame (hybridBridge scalar) adversary parameter auxiliary := by
  rw [congrArg (PMF.bind (PMF.uniformOfFintype NonZeroBase)) (funext fun bridgeKey =>
    shiftedReferenceGame_eq_referenceGame scalar bridgeKey.value adversary parameter auxiliary)]
  exact PMF.bind_const _ _

/-! ### The residual obligation after the transfer -/

/-- The obligation follows from the **charge** alone.

This is `workPerAdvantage_of_steering` with the transfer discharged: what remains of step 7
is the identical-until-bad comparison of the steered reference game with the shifted
reference game. The two have the same sample, the same first stage and the same released
table; they differ only in the second stage, where the steered game programs the steering
gate twice -- honestly and then steered -- and takes two fiber samples, while the shifted
game programs once and samples once at the shifted outputs. Outside the bad event of the
label charge (`uniform_keyLabel_steeringBlocked_le`) the two second stages are *the same law*
(`familyLaw_double`), so the hop costs `3 q₁ / 2 ^ 128` and nothing else. -/
theorem workPerAdvantage_of_steeringCharge [FieldCertificate] [GroupCertificate]
    (adversary : Adversary) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit)
    (charge : advantage
      ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        shiftedReferenceGame (fun _ => bridgeKey.value) scalar adversary parameter auxiliary)
      ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        steeredReferenceGame (fun _ => bridgeKey.value) scalar adversary parameter auxiliary) ≤
      steeringStep adversary parameter) :
    WorkPerAdvantage 100 (adversaryWork adversary parameter)
      (advantage
        (idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) (hybridSimulator scalar)
          idealOracle adversary parameter scalar auxiliary)
        (idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) simulator
          idealOracle adversary parameter scalar auxiliary)) :=
  workPerAdvantage_of_steering adversary parameter scalar auxiliary
    (by rwa [bind_shiftedReferenceGame_eq_referenceGame] at charge)

end

end Kriterion.ArgoMAC.Security
