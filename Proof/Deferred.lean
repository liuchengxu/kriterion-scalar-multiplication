/-
This file proves the deferred-sampling laws of two-stage games.

A two-stage game samples `ω`, runs a first stage that reads only `view ω`,
and then runs a second stage that reads `view ω`, the first-stage result, and
a hidden part `rest r ω` chosen per result. The transfer law says that two such
games agree whenever, for every first-stage result, the joint laws of
`(view ω, rest r ω)` agree: the hidden part may be sampled after the first
stage. The deferred form samples the view first, runs the first stage, and
then samples the hidden part from its conditional law given the view.
-/

import Proof.Logged

namespace Kriterion.ArgoMAC.Security

noncomputable section

/-- A weighted sum over a mapped law is the weighted sum over the source. -/
theorem tsum_map_mul {Source Target : Type} (law : PMF Source) (map : Source → Target)
    (weight : Target → ENNReal) :
    ∑' target, law.map map target * weight target =
      ∑' source, law source * weight (map source) := by
  simp only [PMF.map_apply]
  simp only [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun source => ?_
  rw [tsum_eq_single (map source)]
  · rw [if_pos rfl]
  · intro target different
    rw [if_neg different, zero_mul]

/-- The two-stage game of a sample space: the first stage reads the view, the second
stage reads the view, the hidden part chosen by the first-stage result, and the result. -/
def twoStageGame {Sample View Hidden Result Outcome : Type} (law : PMF Sample)
    (view : Sample → View) (rest : Result → Sample → Hidden)
    (stage1 : View → PMF Result) (stage2 : View → Hidden → Result → PMF Outcome) :
    PMF Outcome :=
  law.bind fun sample => (stage1 (view sample)).bind fun result =>
    stage2 (view sample) (rest result sample) result

/-- The two-stage game in deferred form: sample the view, run the first stage, then
sample the hidden part from its conditional law given the view. -/
def deferredGame {View Hidden Result Outcome : Type} (viewLaw : PMF View)
    (hiddenLaw : Result → View → PMF Hidden)
    (stage1 : View → PMF Result) (stage2 : View → Hidden → Result → PMF Outcome) :
    PMF Outcome :=
  viewLaw.bind fun view => (stage1 view).bind fun result =>
    (hiddenLaw result view).bind fun hidden => stage2 view hidden result

/-- Every two-stage game is a sum, over the first-stage result, of a weighted sum over the
joint law of the view and the hidden part. -/
theorem twoStageGame_apply {Sample View Hidden Result Outcome : Type} (law : PMF Sample)
    (view : Sample → View) (rest : Result → Sample → Hidden)
    (stage1 : View → PMF Result) (stage2 : View → Hidden → Result → PMF Outcome)
    (outcome : Outcome) :
    twoStageGame law view rest stage1 stage2 outcome =
      ∑' result, ∑' pair : View × Hidden,
        law.map (fun sample => (view sample, rest result sample)) pair *
          (stage1 pair.1 result * stage2 pair.1 pair.2 result outcome) := by
  unfold twoStageGame
  simp only [PMF.bind_apply]
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun result => ?_
  rw [tsum_map_mul law (fun sample => (view sample, rest result sample))
    (fun pair => stage1 pair.1 result * stage2 pair.1 pair.2 result outcome)]

/-- The deferred game is the same sum over the factored joint law. -/
theorem deferredGame_apply {View Hidden Result Outcome : Type} (viewLaw : PMF View)
    (hiddenLaw : Result → View → PMF Hidden)
    (stage1 : View → PMF Result) (stage2 : View → Hidden → Result → PMF Outcome)
    (outcome : Outcome) :
    deferredGame viewLaw hiddenLaw stage1 stage2 outcome =
      ∑' result, ∑' pair : View × Hidden,
        jointLaw viewLaw (hiddenLaw result) pair *
          (stage1 pair.1 result * stage2 pair.1 pair.2 result outcome) := by
  unfold deferredGame
  simp only [PMF.bind_apply]
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun result => ?_
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun view => tsum_congr fun hidden => ?_
  rw [jointLaw_apply]
  ring

/-- Transfer law. Two two-stage games agree when, for every first-stage result, the joint
laws of the view and the hidden part agree. -/
theorem twoStageGame_congr {Sample Sample' View Hidden Result Outcome : Type}
    (law : PMF Sample) (law' : PMF Sample') (view : Sample → View) (view' : Sample' → View)
    (rest : Result → Sample → Hidden) (rest' : Result → Sample' → Hidden)
    (stage1 : View → PMF Result) (stage2 : View → Hidden → Result → PMF Outcome)
    (joint : ∀ result, law.map (fun sample => (view sample, rest result sample)) =
      law'.map (fun sample => (view' sample, rest' result sample))) :
    twoStageGame law view rest stage1 stage2 = twoStageGame law' view' rest' stage1 stage2 := by
  ext outcome
  rw [twoStageGame_apply, twoStageGame_apply]
  refine tsum_congr fun result => tsum_congr fun pair => ?_
  rw [joint result]

/-- Deferral law. A two-stage game whose joint law of view and hidden part factors through
the view is the deferred game. -/
theorem twoStageGame_eq_deferredGame {Sample View Hidden Result Outcome : Type}
    (law : PMF Sample) (view : Sample → View) (rest : Result → Sample → Hidden)
    (viewLaw : PMF View) (hiddenLaw : Result → View → PMF Hidden)
    (stage1 : View → PMF Result) (stage2 : View → Hidden → Result → PMF Outcome)
    (joint : ∀ result, law.map (fun sample => (view sample, rest result sample)) =
      jointLaw viewLaw (hiddenLaw result)) :
    twoStageGame law view rest stage1 stage2 = deferredGame viewLaw hiddenLaw stage1 stage2 := by
  ext outcome
  rw [twoStageGame_apply, deferredGame_apply]
  refine tsum_congr fun result => tsum_congr fun pair => ?_
  rw [joint result]

/-- The view of a two-stage game is the marginal of every joint law. -/
theorem map_view_of_joint {Sample View Hidden Result : Type} (law : PMF Sample)
    (view : Sample → View) (rest : Result → Sample → Hidden) (viewLaw : PMF View)
    (hiddenLaw : Result → View → PMF Hidden) (result : Result)
    (joint : law.map (fun sample => (view sample, rest result sample)) =
      jointLaw viewLaw (hiddenLaw result)) :
    law.map view = viewLaw := by
  rw [← jointLaw_map_fst viewLaw (hiddenLaw result), ← joint, PMF.map_comp]
  rfl

end

end Kriterion.ArgoMAC.Security
