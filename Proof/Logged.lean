/-
This file proves the deterministic identical-until-bad law for logged oracle
runs. Two ideal-oracle states with the same log whose views agree on every
query outside a bad set produce the same law of `(result, log)` on every log
that avoids the bad set. A bind form of the challenge's `identical_until_bad`
then bounds the difference of two games that continue such runs by the mass of
the logs that hit the bad set. The log of an ideal-oracle run only grows and
grows by at most the query budget.
-/

import Proof.Simulator

namespace Kriterion.ArgoMAC.Security

open Cryptography

noncomputable section

/-! ### The bind form of identical-until-bad -/

/-- The joint law of a sample and its continuation. -/
def jointLaw {Sample Outcome : Type} (law : PMF Sample) (continuation : Sample → PMF Outcome) :
    PMF (Sample × Outcome) :=
  law.bind fun sample => (continuation sample).map (Prod.mk sample)

theorem jointLaw_apply {Sample Outcome : Type} (law : PMF Sample)
    (continuation : Sample → PMF Outcome) (sample : Sample) (outcome : Outcome) :
    jointLaw law continuation (sample, outcome) = law sample * continuation sample outcome := by
  unfold jointLaw
  rw [PMF.bind_apply]
  rw [tsum_eq_single sample]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single outcome]
    · simp
    · intro other different
      rw [if_neg]
      intro equal
      exact different (Prod.mk.inj equal).2.symm
  · intro other different
    rw [PMF.map_apply]
    refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun value => ?_)
    rw [if_neg]
    intro equal
    exact different (Prod.mk.inj equal).1.symm

theorem jointLaw_map_snd {Sample Outcome : Type} (law : PMF Sample)
    (continuation : Sample → PMF Outcome) :
    (jointLaw law continuation).map Prod.snd = law.bind continuation := by
  unfold jointLaw
  rw [PMF.map_bind]
  refine congrArg (PMF.bind law) (funext fun sample => ?_)
  rw [PMF.map_comp]
  exact PMF.map_id (continuation sample)

theorem jointLaw_map_fst {Sample Outcome : Type} (law : PMF Sample)
    (continuation : Sample → PMF Outcome) :
    (jointLaw law continuation).map Prod.fst = law := by
  unfold jointLaw
  rw [PMF.map_bind]
  have constant : (fun sample => ((continuation sample).map (Prod.mk sample)).map Prod.fst) =
      fun sample => PMF.pure sample := by
    funext sample
    rw [PMF.map_comp]
    change (continuation sample).map (fun _ => sample) = PMF.pure sample
    exact PMF.map_const (continuation sample) sample
  rw [constant, PMF.bind_pure]

/-- Two games that sample laws agreeing off a bad set and continue with the same
continuation off the bad set differ by the bad mass of the second law. -/
theorem bind_identical_until_bad {Sample Outcome : Type} (first second : PMF Sample)
    (firstContinuation secondContinuation : Sample → PMF Outcome) (bad : Set Sample)
    (event : Set Outcome) (agreeLaw : ∀ sample ∉ bad, first sample = second sample)
    (agreeContinuation : ∀ sample ∉ bad, firstContinuation sample = secondContinuation sample) :
    |((first.bind firstContinuation).toOuterMeasure event).toReal -
        ((second.bind secondContinuation).toOuterMeasure event).toReal| ≤
      (second.toOuterMeasure bad).toReal := by
  have joint := Probability.identical_until_bad (jointLaw first firstContinuation)
    (jointLaw second secondContinuation) (Prod.fst ⁻¹' bad) (Prod.snd ⁻¹' event) (by
      rintro ⟨sample, outcome⟩ good
      rw [jointLaw_apply, jointLaw_apply, agreeLaw sample good, agreeContinuation sample good])
  have badMass : second.toOuterMeasure bad =
      (jointLaw second secondContinuation).toOuterMeasure (Prod.fst ⁻¹' bad) := by
    rw [← PMF.toOuterMeasure_map_apply, jointLaw_map_fst]
  rw [← jointLaw_map_snd first firstContinuation, ← jointLaw_map_snd second secondContinuation,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply, badMass]
  exact joint

/-! ### Logged runs -/

/-- The log of an ideal-oracle run keeps every earlier query. -/
theorem run_idealOracle_log_mono {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget)
    (state : State) (output : Result × State)
    (member : output ∈ (program.run idealOracle state).support) (query : Query)
    (seen : query ∈ state.log) : query ∈ output.2.log := by
  induction program generalizing state with
  | pure distribution =>
    rw [OracleProgram.run_pure, PMF.support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact seen
  | query request next inductionHypothesis =>
    rw [OracleProgram.run_query] at member
    exact inductionHypothesis _ _ member (List.mem_cons_of_mem _ seen)
  | sample distribution next inductionHypothesis =>
    rw [OracleProgram.run_sample, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨value, _, member⟩ := member
    exact inductionHypothesis value state member seen

/-- The log of an ideal-oracle run grows by at most the query budget. -/
theorem run_idealOracle_log_length {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget)
    (state : State) (output : Result × State)
    (member : output ∈ (program.run idealOracle state).support) :
    output.2.log.length ≤ state.log.length + budget := by
  induction program generalizing state with
  | pure distribution =>
    rw [OracleProgram.run_pure, PMF.support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact Nat.le_add_right _ _
  | query request next inductionHypothesis =>
    rw [OracleProgram.run_query] at member
    have bound := inductionHypothesis _ _ member
    simp only [idealOracle, List.length_cons] at bound
    omega
  | sample distribution next inductionHypothesis =>
    rw [OracleProgram.run_sample, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨value, _, member⟩ := member
    exact inductionHypothesis value state member

/-- The visible outcome of a logged run: the result and the log. -/
def loggedOutcome {Result : Type} (output : Result × State) : Result × List Query :=
  (output.1, output.2.log)

/-- Two ideal-oracle states with the same log whose views agree off the bad queries give
the same law of `(result, log)` on every log that avoids the bad queries. -/
theorem run_idealOracle_agree {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget)
    (bad : Query → Prop) (first second : State) (sameLog : first.log = second.log)
    (agree : ∀ query, ¬ bad query →
      publicAnswer first.view query = publicAnswer second.view query)
    (result : Result) (log : List Query) (good : ∀ query ∈ log, ¬ bad query) :
    ((program.run idealOracle first).map loggedOutcome) (result, log) =
      ((program.run idealOracle second).map loggedOutcome) (result, log) := by
  induction program generalizing first second with
  | pure distribution =>
    rw [OracleProgram.run_pure, OracleProgram.run_pure, PMF.map_comp, PMF.map_comp]
    have same : (loggedOutcome ∘ fun value : Result => (value, first)) =
        loggedOutcome ∘ fun value => (value, second) := by
      funext value
      simp only [Function.comp, loggedOutcome, sameLog]
    rw [same]
  | query request next inductionHypothesis =>
    rw [OracleProgram.run_query, OracleProgram.run_query]
    by_cases badQuery : bad request
    · have vanish (state : State) :
          ((next (idealOracle request state).1).run idealOracle
            (idealOracle request state).2).map loggedOutcome (result, log) = 0 := by
        rw [PMF.apply_eq_zero_iff, PMF.support_map]
        rintro ⟨output, member, equal⟩
        have seen := run_idealOracle_log_mono _ _ output member request List.mem_cons_self
        have inLog : request ∈ log := by
          rw [← (Prod.mk.inj equal).2]
          exact seen
        exact good request inLog badQuery
      rw [vanish, vanish]
    · have sameAnswer : (idealOracle request first).1 = (idealOracle request second).1 :=
        agree request badQuery
      have nextFirst : (next (idealOracle request first).1) =
          next (idealOracle request second).1 := by
        rw [sameAnswer]
      rw [nextFirst]
      exact inductionHypothesis _ _ _ (by simp only [idealOracle, sameLog]) agree
  | sample distribution next inductionHypothesis =>
    rw [OracleProgram.run_sample, OracleProgram.run_sample, PMF.map_bind, PMF.map_bind,
      PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun value => ?_
    rw [inductionHypothesis value first second sameLog agree]

end

end Kriterion.ArgoMAC.Security
