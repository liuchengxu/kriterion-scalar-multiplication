/-
This file assembles the entry: the executable construction of `Construction`
together with the proofs of `Proof`, in the exact field order of
`Kriterion.Solution`.

Every data field is computable -- the metric runs the entry -- and every
noncomputable witness the proof needs (the tape law, the simulator, the uniform
oracle law) sits behind a `Prop` field, so the bundle itself compiles.
-/

import Solution
import Construction
import Proof

namespace Submission

open Kriterion Kriterion.BN254 Kriterion.ArgoMAC

/-- The BN254 scalar-multiplication entry: the curve-membership garbling of
`Construction`, its 40768-byte wire format, and the adaptive-privacy proof of
`Proof`. -/
def solution : Kriterion.Solution where
  FixedIndex := FixedKeyIndex
  EncIndex := Garbling.EncIndex
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Garbling.Randomness
  randomnessFinite := inferInstance
  randomness := Security.witnessTape
  Public := Garbling.Public
  EncodingKey := Garbling.EncodingKey
  State := Security.State
  encoding := Wire.encoding
  ciphertextBytes := 40768
  evaluationOracle := Garbling.evaluationOracle
  oracleUniform :=
    Security.standardAssumptions_congr _ _ _ _ _ _ _ _
      (Security.oracleUniform Security.witnessTape)
  scheme := fun field group => @Garbling.garbledCircuit field group
  ciphertextSize := by
    intro field group parameter scalar tape
    dsimp only [Garbling.garbledCircuit]
    exact Wire.garble_encode_length parameter scalar tape
  lamportCompatible := fun field group => @Lamport.compatible field group
  idealOracle := Security.idealOracle
  idealView := Security.idealView
  functionCorrect := fun field group scalar input =>
    @Garbling.functionCorrect field group scalar input
  perfectCorrectness := fun field group => @Garbling.perfectCorrectness field group
  adaptivePrivacy := fun field group =>
    ⟨@Security.simulator field group, @Security.oracleSimulation field group,
      @Security.adaptivePrivacy field group Security.witnessTape⟩

end Submission
