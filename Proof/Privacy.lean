/-
This file states the adaptive-privacy obligation for the scheme and reduces it
to two named lemmas: the marginal match and steering invisibility.

The hybrid game is the real game written in the simulator's shape: its first
stage samples the same tape and carrier as the simulator but garbles the curve
table for the bridge key `carrier / scalar`, so the honest labels already
release `carrier / scalar` and no programming is needed. The first lemma is the
marginal match: the real game equals the hybrid game. The second lemma is
steering invisibility: the hybrid game and the simulated game differ only where
the adversary hits a programmed or hidden label point, which the chain of games
of `Proof/Chain.lean` charges hop by hop.

The hybrid game and the shared core live in `Proof/Hybrid.lean`, upstream of the
chain; this file is the last one, so it can consume the chain's own conclusion.
-/

import Proof.Hybrid
import Proof.SteeringHop

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

noncomputable section

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
          idealOracle adversary parameter scalar auxiliary)) :=
  workPerAdvantage_of_steeringCharge adversary parameter scalar auxiliary
    (le_trans
      (advantage_shiftedReferenceGame_steeredReferenceGame_le scalar adversary parameter
        auxiliary)
      (steeringCharge_le_steeringStep adversary parameter))

/-- The adaptive-privacy obligation follows from the two lemmas above. -/
theorem adaptivePrivacy [FieldCertificate] [GroupCertificate] (witness : Garbling.Randomness) :
    ConcreteAdaptivePrivacy (Aux := Unit) Garbling.garbledCircuit (fun _ => ciphertextBytes)
      simulator (realTape witness) (publicHandler Garbling.evaluationOracle) idealOracle 100 := by
  intro adversary circuit auxiliary parameter
  rw [realGame_eq_hybridGame]
  exact hybridGame_close_to_idealGame adversary parameter (circuit parameter) (auxiliary parameter)

end

end Kriterion.ArgoMAC.Security

