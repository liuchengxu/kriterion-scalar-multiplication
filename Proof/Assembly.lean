/-
This file assembles the chain of games into the adaptive-privacy obligation,
leaving exactly one probabilistic input open: the steering hop.

Both sides of the chain are machine-checked and both end at a reference game.
The hybrid side reaches `R(carrier / scalar)` (`advantage_hybridGame_referenceGame_le`)
and the simulated side reaches `R(u)` plus the steering, with `u` the tape's own
bridge key (`advantage_simulatedGame_steeredReferenceGame_le`). What is left is the
identification of those two middle games -- step 7 of the architecture -- and this
file shows that the identification is the *only* thing left: given it as a
hypothesis, at the share of the budget the accounting reserves for it, the
obligation follows by two triangle inequalities and `workPerAdvantage_of_chain`.

Keeping the hop as a hypothesis rather than as a second unproved
declaration means the accounting itself is machine-checked: the three shares sum to
`chainPerQuery * q / 2 ^ 128 + chainOneTime`, so the value of `chainPerQuery`
is validated end to end and the residual obligation is one crisp inequality
between two explicitly named games.
-/

import Proof.SimulatedReference

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography GarbledCircuit Cryptography.Assumptions

noncomputable section

/-- The share of the budget the accounting reserves for the steering hop: eight points per
log entry (three permutation points charged at `1 / (2 ^ 128 - q) ≤ 2 / 2 ^ 128` and one
hash-fiber chunk charged at `2 / 2 ^ 128`, in each query direction), plus the one-time
freshness term of the two chunks the reparametrisation swaps. -/
def steeringStep (adversary : Adversary) (parameter : Nat) : ℝ :=
  8 * ((adversary.firstQueryBudget parameter +
    adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 + 6 / 2 ^ 128

/-- The three shares of the chain sum to exactly the budget `workPerAdvantage_of_chain`
consumes. -/
theorem chain_shares_eq (adversary : Adversary) (parameter : Nat) :
    (4 * ((adversary.firstQueryBudget parameter +
          adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 + sideOneTime) +
        (steeringStep adversary parameter +
          (4 * ((adversary.firstQueryBudget parameter +
            adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 + sideOneTime)) =
      chainPerQuery * ((adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 + chainOneTime := by
  unfold steeringStep chainPerQuery chainOneTime
  ring

/-- The obligation follows from the steering hop alone.

The hypothesis is step 7 of the architecture: the reference game of the hybrid side's
bridge key `carrier / scalar` is within the steering hop's share of the budget of the
simulated side's steered reference game of the tape's own bridge key `u`. Everything else
in the chain is already proved. -/
theorem workPerAdvantage_of_steering [FieldCertificate] [GroupCertificate]
    (adversary : Adversary) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Unit)
    (steering : advantage (referenceGame (hybridBridge scalar) adversary parameter auxiliary)
      ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        steeredReferenceGame (fun _ => bridgeKey.value) scalar adversary parameter auxiliary) ≤
      steeringStep adversary parameter) :
    WorkPerAdvantage 100 (adversaryWork adversary parameter)
      (advantage
        (idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) (hybridSimulator scalar)
          idealOracle adversary parameter scalar auxiliary)
        (idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) simulator
          idealOracle adversary parameter scalar auxiliary)) := by
  have steered : advantage
      ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        steeredReferenceGame (fun _ => bridgeKey.value) scalar adversary parameter auxiliary)
      (idealGame Garbling.garbledCircuit (fun _ => ciphertextBytes) simulator idealOracle
        adversary parameter scalar auxiliary) ≤
      4 * ((adversary.firstQueryBudget parameter +
        adversary.secondQueryBudget parameter : Nat) : ℝ) / 2 ^ 128 + sideOneTime := by
    rw [advantage_comm]
    exact advantage_simulatedGame_steeredReferenceGame_le adversary parameter scalar auxiliary
  refine workPerAdvantage_of_chain adversary parameter _ ?_
  refine le_trans (advantage_trans _ (referenceGame (hybridBridge scalar) adversary parameter
    auxiliary) _ _ _
      (advantage_hybridGame_referenceGame_le adversary parameter scalar auxiliary)
      (advantage_trans _ ((PMF.uniformOfFintype NonZeroBase).bind fun bridgeKey =>
        steeredReferenceGame (fun _ => bridgeKey.value) scalar adversary parameter auxiliary)
        _ _ _ steering steered)) ?_
  exact le_of_eq (chain_shares_eq adversary parameter)

end

end Kriterion.ArgoMAC.Security
