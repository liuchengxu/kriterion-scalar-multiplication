/-
This file proves the challenge's standard-assumption certificate: the tape law
projects onto the public oracle triple exactly uniformly.

The tape is a product in disguise. Its three public fields -- the fixed-key
permutation family, the unused encryption family and the hash table -- are
exactly the projection `Garbling.evaluationOracle`, and the remaining fields are
the tapes on which those three are pinned to fixed values. Splitting the tape
along that product turns the uniform tape law into a uniform product law, whose
first marginal is the uniform public oracle.
-/

import Proof.Finite
import Cryptography.Assumptions

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-! ### Uniform product facts -/

/-- An equivalence preserves finite uniform mass. -/
theorem uniform_map_equiv {Source Target : Type*}
    [Fintype Source] [Nonempty Source] [Fintype Target] [Nonempty Target]
    (equivalence : Source ≃ Target) :
    (PMF.uniformOfFintype Source).map equivalence = PMF.uniformOfFintype Target :=
  PMF.uniformOfFintype_map_of_bijective equivalence equivalence.bijective

/-- The first coordinate of a uniform product is uniform. -/
theorem uniform_map_fst {First Second : Type*}
    [Fintype First] [Nonempty First] [Fintype Second] [Nonempty Second] :
    (PMF.uniformOfFintype (First × Second)).map Prod.fst = PMF.uniformOfFintype First := by
  classical
  apply PMF.ext
  intro output
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod]
  rw [ENNReal.tsum_prod']
  push_cast
  rw [ENNReal.mul_inv] <;> try simp [Fintype.card_ne_zero]
  rw [mul_left_comm, ENNReal.mul_inv_cancel]
  · simp
  · exact_mod_cast Fintype.card_ne_zero
  · simp

/-! ### The tape splits along its public tables -/

/-- The tape with its three public tables pinned to fixed values. -/
def pinTables (tape : Garbling.Randomness) : Garbling.Randomness :=
  { tape with
    fixedKeyOracle := ⟨fun _ => Equiv.refl Block⟩
    encOracle := ⟨fun _ => Equiv.refl Block⟩
    hashOracle := fun _ => (0, 0) }

/-- The tapes whose public tables are already pinned: everything the public
oracle triple does not see. -/
abbrev PrivateTape := { tape : Garbling.Randomness // pinTables tape = tape }

/-- The tape is the public oracle triple together with the pinned remainder. -/
def splitTape : Garbling.Randomness ≃
    PublicOracle FixedKeyIndex Garbling.EncIndex × PrivateTape where
  toFun tape := (Garbling.evaluationOracle tape, ⟨pinTables tape, rfl⟩)
  invFun pair :=
    { pair.2.1 with
      fixedKeyOracle := pair.1.1
      encOracle := pair.1.2.1
      hashOracle := pair.1.2.2 }
  left_inv tape := by cases tape; rfl
  right_inv pair := by
    rcases pair with ⟨⟨fixed, enc, hash⟩, ⟨tape, pinned⟩⟩
    exact Prod.ext rfl (Subtype.ext pinned)

/-- The certificate does not depend on which finite-type instances state it. The
challenge states it at `Fintype.ofFinite`; the proof states it at the tape's own
instances. -/
theorem standardAssumptions_congr {FixedIndex EncIndex Tape : Type}
    (fixedFirst fixedSecond : Fintype FixedIndex) (encFirst encSecond : Fintype EncIndex)
    (tapeFirst tapeSecond : Fintype Tape) (witness : Tape)
    (project : Tape → PublicOracle FixedIndex EncIndex)
    (certificate : @Cryptography.Assumptions.StandardAssumptions FixedIndex EncIndex Tape
      fixedFirst encFirst tapeFirst witness project) :
    @Cryptography.Assumptions.StandardAssumptions FixedIndex EncIndex Tape
      fixedSecond encSecond tapeSecond witness project := by
  obtain rfl : fixedSecond = fixedFirst := Subsingleton.elim _ _
  obtain rfl : encSecond = encFirst := Subsingleton.elim _ _
  obtain rfl : tapeSecond = tapeFirst := Subsingleton.elim _ _
  exact certificate

/-- The public tables have the joint uniform law the challenge requires. -/
theorem oracleUniform (witness : Garbling.Randomness) :
    Cryptography.Assumptions.StandardAssumptions FixedKeyIndex Garbling.EncIndex
      Garbling.Randomness witness Garbling.evaluationOracle := by
  classical
  letI : Fintype PrivateTape := Fintype.ofFinite PrivateTape
  letI : Nonempty PrivateTape := ⟨⟨pinTables witness, rfl⟩⟩
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  rw [Cryptography.Assumptions.StandardAssumptions, Cryptography.uniformTape_eq]
  have mapped := congrArg (PMF.map Prod.fst) (uniform_map_equiv splitTape)
  rw [uniform_map_fst] at mapped
  simpa only [PMF.map_comp, Function.comp_def, splitTape, Equiv.coe_fn_mk] using mapped

end

end Kriterion.ArgoMAC.Security
