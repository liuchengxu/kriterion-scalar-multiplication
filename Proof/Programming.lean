/-
This file proves the programming bijection. Programming a permutation at a
label to a fresh value, while remembering the old value at that label, is an
involution of `permutation × value`. A uniform permutation is therefore the
same law as a uniform permutation programmed at any label to an independent
uniform value; the family version reparametrizes the whole fixed-key oracle by
programming every index at its own label.
-/

import Proof.Simulator
import Proof.Uniform

namespace Kriterion.ArgoMAC.Security

open Cryptography

/-- Program `permutation` at `label` to `value`, and remember the old image of `label`. -/
def programAt (label : Block) (pair : Equiv Block Block × Block) : Equiv Block Block × Block :=
  (pair.1.trans (Equiv.swap (pair.1 label) pair.2), pair.1 label)

theorem programAt_programAt (label : Block) (pair : Equiv Block Block × Block) :
    programAt label (programAt label pair) = pair := by
  obtain ⟨permutation, value⟩ := pair
  simp only [programAt, Equiv.trans_apply, Equiv.swap_apply_left, Prod.mk.injEq, and_true]
  rw [Equiv.trans_assoc, Equiv.swap_comm value (permutation label), Equiv.swap_swap,
    Equiv.trans_refl]

/-- Programming at a label is an involution of `permutation × value`. -/
def programAtEquiv (label : Block) : Equiv Block Block × Block ≃ Equiv Block Block × Block where
  toFun := programAt label
  invFun := programAt label
  left_inv := programAt_programAt label
  right_inv := programAt_programAt label

noncomputable section

/-- A uniform permutation is a uniform permutation programmed at `label` to an
independent uniform value. -/
theorem uniform_programAt (label : Block) :
    (PMF.uniformOfFintype (Equiv Block Block × Block)).map
        (fun pair => (programAt label pair).1) =
      PMF.uniformOfFintype (Equiv Block Block) := by
  have split : (fun pair : Equiv Block Block × Block => (programAt label pair).1) =
      Prod.fst ∘ programAtEquiv label := rfl
  rw [split, ← PMF.map_comp, uniformOfFintype_map_equiv]
  have unprod : ((PMF.uniformOfFintype (Equiv Block Block × Block)).map Prod.fst) =
      (PMF.uniformOfFintype (Equiv Block Block)).bind fun permutation =>
        (PMF.uniformOfFintype Block).bind fun _ => PMF.pure permutation := by
    rw [PMF.map, uniformOfFintype_bind_prod fun permutation (_ : Block) => PMF.pure permutation]
    rfl
  rw [unprod]
  simp only [PMF.bind_const, PMF.bind_pure]

/-- Program every index of a fixed-key oracle at its own label, remembering the old images. -/
def programFamily (labels : FixedKeyIndex → Block)
    (pair : PermutationOracle FixedKeyIndex Block × (FixedKeyIndex → Block)) :
    PermutationOracle FixedKeyIndex Block × (FixedKeyIndex → Block) :=
  (⟨fun index => (programAt (labels index) (pair.1.permutation index, pair.2 index)).1⟩,
    fun index => (programAt (labels index) (pair.1.permutation index, pair.2 index)).2)

theorem programFamily_programFamily (labels : FixedKeyIndex → Block)
    (pair : PermutationOracle FixedKeyIndex Block × (FixedKeyIndex → Block)) :
    programFamily labels (programFamily labels pair) = pair := by
  obtain ⟨⟨permutation⟩, values⟩ := pair
  simp only [programFamily, Prod.mk.injEq, PermutationOracle.mk.injEq]
  constructor
  · funext index
    exact congrArg Prod.fst (programAt_programAt (labels index) (permutation index, values index))
  · funext index
    exact congrArg Prod.snd (programAt_programAt (labels index) (permutation index, values index))

/-- Programming every index at its own label is an involution. -/
def programFamilyEquiv (labels : FixedKeyIndex → Block) :
    PermutationOracle FixedKeyIndex Block × (FixedKeyIndex → Block) ≃
      PermutationOracle FixedKeyIndex Block × (FixedKeyIndex → Block) where
  toFun := programFamily labels
  invFun := programFamily labels
  left_inv := programFamily_programFamily labels
  right_inv := programFamily_programFamily labels

/-- A uniform fixed-key oracle is a uniform oracle programmed at every index's label to
independent uniform values. -/
theorem uniform_programFamily (labels : FixedKeyIndex → Block) :
    (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block × (FixedKeyIndex → Block))).map
        (fun pair => (programFamily labels pair).1) =
      PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block) := by
  have split : (fun pair : PermutationOracle FixedKeyIndex Block × (FixedKeyIndex → Block) =>
      (programFamily labels pair).1) = Prod.fst ∘ programFamilyEquiv labels := rfl
  rw [split, ← PMF.map_comp, uniformOfFintype_map_equiv]
  have unprod : ((PMF.uniformOfFintype
      (PermutationOracle FixedKeyIndex Block × (FixedKeyIndex → Block))).map Prod.fst) =
      (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype (FixedKeyIndex → Block)).bind fun _ => PMF.pure oracle := by
    rw [PMF.map, uniformOfFintype_bind_prod
      fun oracle (_ : FixedKeyIndex → Block) => PMF.pure oracle]
    rfl
  rw [unprod]
  simp only [PMF.bind_const, PMF.bind_pure]

end

end Kriterion.ArgoMAC.Security
