/-
This file proves that the garbling tape is a finite type. The tape law of the
challenge samples the complete tape uniformly, so every tape field needs a
`Fintype` instance. The permutation-oracle instance from the challenge library
is noncomputable, so the tape instance lives here rather than under
`Construction/`.
-/

import Construction
import Mathlib.Data.Fintype.EquivFin

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-- Finite vectors are equivalent to finite-index functions. -/
def vectorFunctionEquiv {Value : Type} {count : Nat} :
    (Fin count → Value) ≃ Vector Value count where
  toFun := Vector.ofFn
  invFun := fun values index => values.get index
  left_inv function := by
    funext index
    change (Vector.ofFn function).get index = function index
    rw [Vector.get_ofFn]
  right_inv values := by
    apply Vector.ext
    intro index inRange
    simp only [Vector.getElem_ofFn]
    rfl

instance vectorFintype {Value : Type} {count : Nat} [Fintype Value] :
    Fintype (Vector Value count) :=
  Fintype.ofEquiv (Fin count → Value) vectorFunctionEquiv

instance nonZeroBaseFintype : Fintype NonZeroBase :=
  Fintype.ofInjective NonZeroBase.value (by
    intro first second equal
    cases first
    cases second
    cases equal
    rfl)

instance bitAdaptorKeyFintype : Fintype BitAdaptor.Key :=
  Fintype.ofInjective (fun key => (key.falseLabel, key.trueLabel)) (by
    intro first second equal
    cases first
    cases second
    cases equal
    rfl)

instance inputMacKeyFintype : Fintype InputMacKey :=
  Fintype.ofInjective (fun key => (key.x, key.y)) (by
    intro first second equal
    cases first
    cases second
    cases equal
    rfl)

/-- The tape fields as one tuple. -/
def Garbling.Randomness.data (randomness : Garbling.Randomness) :
    NonZeroBase × NonZeroBase × BaseField × BaseField ×
      PermutationOracle FixedKeyIndex Block × InputMacKey ×
      PermutationOracle Garbling.EncIndex Block × (BaseField → Block × Block) :=
  (randomness.bridgeKey, randomness.curveMask, randomness.curveR1, randomness.curveR2,
    randomness.fixedKeyOracle, randomness.inputMacKey, randomness.encOracle,
    randomness.hashOracle)

theorem Garbling.Randomness.data_injective :
    Function.Injective Garbling.Randomness.data := by
  intro first second equal
  cases first
  cases second
  cases equal
  rfl

instance garblingRandomnessFintype : Fintype Garbling.Randomness :=
  Fintype.ofInjective Garbling.Randomness.data Garbling.Randomness.data_injective

/-- The challenge's tape law needs the tape to be finite. -/
example : Finite Garbling.Randomness := inferInstance

example : Finite FixedKeyIndex := inferInstance

end

end Kriterion.ArgoMAC.Security
