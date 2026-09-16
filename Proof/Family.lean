/-
This file generalises the lazy-sampling model of `Proof/Lazy.lean` from **one**
tracked fixed-key permutation to the **whole family**.

`Proof/Lazy.lean` conditions a single index: its eager side is a run whose
oracle at that index is a separately sampled permutation, and the other indices
stay eager inside the state. That is enough to *bound* one piece of a bad set,
but not enough for the steering hop, whose law equality (`compatibleLaw_double`)
has to be applied at the two or three indices the steering programs **at once**.
A second application cannot be nested inside the first, because the left-hand
side of `compatibleLaw_run` is an eager `program.run idealOracle`; and taking one
hybrid hop per index multiplies the crude charge by the number of indices, which
does not fit the hop's share of the budget.

The family version fixes both. The transcript is one `Assignment` per index, the
conditional law is the product of the per-index conditional laws, and a lazy run
answers *every* fixed-key query from the transcript of its own index. So:

* the hop is **one** application (`uniform_run_familyLaw`), and the eager side is
  literally the uniform permutation family the games sample -- no `setOracleAt`
  bookkeeping;
* the keying is automatic: a query pins a point at its own index only, so the
  budget is `familyPinnedCount`, the **sum** over indices, and it grows by at
  most one per query (`lazyFamilyRun_pinnedCount`);
* the law equality is applied coordinatewise in one step
  (`familyLaw_double`), built on the product-law substitution lemma
  `productPMF_bind_pointwise`.

Nothing here is a new probabilistic argument: the per-index marginalisations are
`compatibleLaw_forward` / `compatibleLaw_inverse` of `Proof/Lazy.lean` and the
per-index law equality is `compatibleLaw_double` of `Proof/Erased.lean`. What is
new is the product bookkeeping, which is `Proof/Product.lean`'s
`productPMF_bind_update` read in both directions.
-/

import Proof.Erased

namespace Kriterion.ArgoMAC.Security

open Cryptography

noncomputable section

/-! ### Reading one coordinate of a product law -/

section Product

variable {Index Value Outcome : Type} [Fintype Index] [DecidableEq Index] [Fintype Value]
  [DecidableEq Value]

/-- One coordinate of a product law may be drawn first: sampling the whole family and then
overwriting one coordinate with a fresh draw from that coordinate's own law is the same
family. -/
theorem productPMF_bind_place (laws : Index → PMF Value) (place : Index)
    (continuation : (Index → Value) → PMF Outcome) :
    (productPMF laws).bind continuation =
      (laws place).bind fun value =>
        (productPMF laws).bind fun values => continuation (Function.update values place value) := by
  have inner : (fun values : Index → Value =>
        ((laws place).map fun value => Function.update values place value).bind continuation) =
      fun values : Index → Value => (laws place).bind fun value =>
        continuation (Function.update values place value) :=
    funext fun _ => bind_of_map _ _ _
  have step : (((productPMF laws).bind fun values =>
        (laws place).map fun value => Function.update values place value).bind continuation) =
      (laws place).bind fun value =>
        (productPMF laws).bind fun values =>
          continuation (Function.update values place value) := by
    rw [PMF.bind_bind, inner]
    exact PMF.bind_comm _ _ _
  rw [← step, productPMF_bind_update laws place (laws place), Function.update_eq_self]

/-- Replacing one coordinate's law is invisible to a continuation that never reads that
coordinate. -/
theorem productPMF_bind_update_unread (laws : Index → PMF Value) (place : Index)
    (fresh : PMF Value) (continuation : (Index → Value) → PMF Outcome)
    (unread : ∀ (values : Index → Value) (value : Value),
      continuation (Function.update values place value) = continuation values) :
    (productPMF (Function.update laws place fresh)).bind continuation =
      (productPMF laws).bind continuation := by
  have base := productPMF_bind_update_congr laws place fresh (laws place) continuation unread
  rwa [Function.update_eq_self] at base

/-- The split form of a product law whose coordinate at `place` is drawn from another law. -/
theorem productPMF_bind_place_update (laws : Index → PMF Value) (place : Index)
    (fresh : PMF Value) (continuation : (Index → Value) → PMF Outcome) :
    (productPMF (Function.update laws place fresh)).bind continuation =
      fresh.bind fun value =>
        (productPMF laws).bind fun values => continuation (Function.update values place value) := by
  rw [productPMF_bind_place (Function.update laws place fresh) place continuation,
    Function.update_self]
  refine congrArg (PMF.bind _) (funext fun value => ?_)
  refine productPMF_bind_update_unread laws place fresh
    (fun values => continuation (Function.update values place value)) fun values other => ?_
  rw [Function.update_idem]

/-- Every coordinate of a sample of a product law is a sample of its own law. -/
theorem productPMF_support_mem (laws : Index → PMF Value) {values : Index → Value}
    (member : values ∈ (productPMF laws).support) (place : Index) :
    values place ∈ (laws place).support := by
  rw [PMF.mem_support_iff, productPMF_apply] at member
  rw [PMF.mem_support_iff]
  exact (Finset.prod_ne_zero_iff.mp member) place (Finset.mem_univ place)

/-- Substituting one law-preserving transform per coordinate. Each coordinate's transform
may be replaced by another one that gives the same law under every continuation; the
replacement is then invisible on the whole product. This is the coordinatewise form the
steering hop needs: it programs two or three indices, and each index's substitution is the
same law equality. -/
theorem productPMF_bind_pointwise (laws : Index → PMF Value)
    (first second : Index → Value → Value) (continuation : (Index → Value) → PMF Outcome)
    (pointwise : ∀ (place : Index) (cont : Value → PMF Outcome),
      ((laws place).bind fun value => cont (first place value)) =
        (laws place).bind fun value => cont (second place value)) :
    ((productPMF laws).bind fun values => continuation fun index => first index (values index)) =
      (productPMF laws).bind fun values =>
        continuation fun index => second index (values index) := by
  classical
  set mix : Finset Index → Index → Value → Value :=
    fun chosen index value =>
      if index ∈ chosen then first index value else second index value with mixDef
  have step : ∀ chosen : Finset Index,
      ((productPMF laws).bind fun values =>
          continuation fun index => mix chosen index (values index)) =
        (productPMF laws).bind fun values =>
          continuation fun index => second index (values index) := by
    intro chosen
    induction chosen using Finset.induction with
    | empty =>
      have same : mix ∅ = second := by
        funext index value
        simp only [mixDef, Finset.notMem_empty, if_false]
      rw [same]
    | insert place chosen absent inductionHypothesis =>
      refine Eq.trans ?_ inductionHypothesis
      have rewrite : ∀ (transform : Index → Value → Value),
          (∀ index, index ≠ place → transform index = mix chosen index) →
          ∀ (values : Index → Value) (value : Value),
            (fun index => transform index ((Function.update values place value) index)) =
              Function.update (fun index => mix chosen index (values index)) place
                (transform place value) := by
        intro transform agree values value
        funext index
        by_cases same : index = place
        · subst same
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne same, Function.update_of_ne same, agree index same]
      have insertedAgree : ∀ index, index ≠ place →
          mix (insert place chosen) index = mix chosen index := by
        intro index different
        funext value
        simp only [mixDef, Finset.mem_insert, different, false_or]
      have chosenAgree : ∀ index, index ≠ place → mix chosen index = mix chosen index :=
        fun _ _ => rfl
      have insertedPlace : mix (insert place chosen) place = first place := by
        funext value
        simp only [mixDef, Finset.mem_insert, true_or, if_true]
      have chosenPlace : mix chosen place = second place := by
        funext value
        simp only [mixDef, if_neg absent]
      have expand : ∀ transform : Index → Value → Value,
          (∀ index, index ≠ place → transform index = mix chosen index) →
          ((productPMF laws).bind fun values =>
              continuation fun index => transform index (values index)) =
            (laws place).bind fun value =>
              (productPMF laws).bind fun values =>
                continuation (Function.update (fun index => mix chosen index (values index))
                  place (transform place value)) := by
        intro transform agree
        rw [productPMF_bind_place laws place
          (fun values => continuation fun index => transform index (values index))]
        refine congrArg (PMF.bind _) (funext fun value => ?_)
        refine congrArg (PMF.bind _) (funext fun values => ?_)
        rw [rewrite transform agree values value]
      rw [expand (mix (insert place chosen)) insertedAgree,
        expand (mix chosen) chosenAgree, insertedPlace, chosenPlace]
      exact pointwise place fun value =>
        (productPMF laws).bind fun values =>
          continuation (Function.update (fun index => mix chosen index (values index)) place value)
  have full : mix Finset.univ = first := by
    funext index value
    simp only [mixDef, Finset.mem_univ, if_true]
  rw [← full]
  exact step Finset.univ

end Product

/-! ### A transcript per index -/

/-- A transcript for every fixed-key index: what the adversary has learned about each of
the independent permutations. -/
abbrev FamilyAssignment := FixedKeyIndex → Assignment

/-- Every index's transcript is injective. -/
def FamilyInjective (assigns : FamilyAssignment) : Prop :=
  ∀ index, AssignmentInjective (assigns index)

/-- Pin one input of one index's transcript to one value. -/
def pinFamily (assigns : FamilyAssignment) (index : FixedKeyIndex) (input value : Block) :
    FamilyAssignment :=
  Function.update assigns index (Function.update (assigns index) input (some value))

theorem pinFamily_self (assigns : FamilyAssignment) (index : FixedKeyIndex)
    (input value : Block) :
    pinFamily assigns index input value index =
      Function.update (assigns index) input (some value) := by
  rw [pinFamily, Function.update_self]

theorem pinFamily_of_ne (assigns : FamilyAssignment) (index other : FixedKeyIndex)
    (input value : Block) (different : other ≠ index) :
    pinFamily assigns index input value other = assigns other := by
  rw [pinFamily, Function.update_of_ne different]

theorem pinFamily_injective (assigns : FamilyAssignment) (injective : FamilyInjective assigns)
    (index : FixedKeyIndex) (input value : Block)
    (unused : value ∉ pinnedRange (assigns index)) :
    FamilyInjective (pinFamily assigns index input value) := by
  intro other
  by_cases same : other = index
  · subst same
    rw [pinFamily_self]
    exact update_injective (assigns other) (injective other) input value unused
  · rw [pinFamily_of_ne assigns index other input value same]
    exact injective other

noncomputable instance instDecidableEqBlockEquiv : DecidableEq (Equiv Block Block) :=
  fun first second => Classical.propDecidable (first = second)

/-- The permutation family read as a function of its indices. -/
def oracleEquiv :
    (FixedKeyIndex → Equiv Block Block) ≃ PermutationOracle FixedKeyIndex Block where
  toFun permutations := ⟨permutations⟩
  invFun oracle := oracle.permutation
  left_inv _ := rfl
  right_inv _ := rfl

/-- The law of the whole permutation family given one transcript per index: every index is
independently uniform over the permutations compatible with its own transcript. -/
def familyLaw (assigns : FamilyAssignment) : PMF (PermutationOracle FixedKeyIndex Block) :=
  (productPMF fun index => compatibleLaw (assigns index)).map oracleEquiv

theorem familyLaw_bind {Result : Type} (assigns : FamilyAssignment)
    (continuation : PermutationOracle FixedKeyIndex Block → PMF Result) :
    (familyLaw assigns).bind continuation =
      (productPMF fun index => compatibleLaw (assigns index)).bind fun permutations =>
        continuation ⟨permutations⟩ := by
  show ((productPMF fun index => compatibleLaw (assigns index)).map oracleEquiv).bind
    continuation = _
  refine Eq.trans (bind_of_map _ _ _) ?_
  exact congrArg (PMF.bind _) (funext fun _ => rfl)

/-- Every permutation of a sample of the family law is compatible with its own
transcript. -/
theorem familyLaw_support (assigns : FamilyAssignment) (injective : FamilyInjective assigns)
    {oracle : PermutationOracle FixedKeyIndex Block}
    (member : oracle ∈ (familyLaw assigns).support) (index : FixedKeyIndex) :
    Compatible (assigns index) (oracle.permutation index) := by
  obtain ⟨permutations, permutationsMember, equal⟩ :=
    exists_mem_support_of_mem_support_map _ oracleEquiv member
  have same : oracle.permutation index = permutations index := by rw [← equal]; rfl
  rw [same]
  exact compatibleLaw_support (assigns index) (injective index)
    (productPMF_support_mem _ permutationsMember index)

/-- Before any query the conditional law of the family is the uniform permutation family.
This is the bridge from the games, which sample exactly that law. -/
theorem familyLaw_empty :
    familyLaw (fun _ _ => none) =
      PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block) := by
  have laws : (fun index : FixedKeyIndex =>
      compatibleLaw ((fun _ _ => none : FamilyAssignment) index)) =
      fun _ : FixedKeyIndex => PMF.uniformOfFintype (Equiv Block Block) :=
    funext fun _ => compatibleLaw_empty
  show (productPMF fun index => compatibleLaw ((fun _ _ => none : FamilyAssignment) index)).map
    oracleEquiv = _
  rw [laws, ← uniformOfFintype_pi]
  exact uniformOfFintype_map_bijection oracleEquiv

/-! ### The two marginalisations, per index -/

theorem familyLaw_laws_pinFamily (assigns : FamilyAssignment) (index : FixedKeyIndex)
    (input value : Block) :
    (fun other => compatibleLaw (pinFamily assigns index input value other)) =
      Function.update (fun other => compatibleLaw (assigns other)) index
        (compatibleLaw (Function.update (assigns index) input (some value))) := by
  funext other
  by_cases same : other = index
  · subst same
    rw [pinFamily_self, Function.update_self]
  · rw [pinFamily_of_ne assigns index other input value same, Function.update_of_ne same]

/-- Reading the family at one index, at an input that index's transcript has not pinned, is
the same as drawing the answer from that index's fresh values first and conditioning the
family on it. -/
theorem familyLaw_forward {Result : Type} (assigns : FamilyAssignment)
    (injective : FamilyInjective assigns) (index : FixedKeyIndex) (input : Block)
    (fresh : assigns index input = none)
    (continuation : Block → PermutationOracle FixedKeyIndex Block → PMF Result) :
    ((familyLaw assigns).bind fun oracle =>
        continuation (oracle.permutation index input) oracle) =
      (freshValueLaw (assigns index)).bind fun value =>
        (familyLaw (pinFamily assigns index input value)).bind fun oracle =>
          continuation value oracle := by
  have base : ((familyLaw assigns).bind fun oracle =>
        continuation (oracle.permutation index input) oracle) =
      (compatibleLaw (assigns index)).bind fun permutation =>
        (productPMF fun other => compatibleLaw (assigns other)).bind fun permutations =>
          continuation ((Function.update permutations index permutation) index input)
            ⟨Function.update permutations index permutation⟩ :=
    (familyLaw_bind assigns _).trans (productPMF_bind_place _ index _)
  simp only [Function.update_self] at base
  rw [base, compatibleLaw_forward (assigns index) (injective index) input fresh
    (fun answer permutation =>
      (productPMF fun other => compatibleLaw (assigns other)).bind fun permutations =>
        continuation answer ⟨Function.update permutations index permutation⟩)]
  refine congrArg (PMF.bind _) (funext fun value => ?_)
  have right : ((familyLaw (pinFamily assigns index input value)).bind fun oracle =>
        continuation value oracle) =
      (compatibleLaw (Function.update (assigns index) input (some value))).bind
        fun permutation =>
          (productPMF fun other => compatibleLaw (assigns other)).bind fun permutations =>
            continuation value ⟨Function.update permutations index permutation⟩ := by
    refine Eq.trans (familyLaw_bind _ _) ?_
    rw [familyLaw_laws_pinFamily assigns index input value]
    exact productPMF_bind_place_update _ index _ _
  exact right.symm

/-- Inverting the family at one index, at a value that index's transcript has not used, is
the same as drawing the preimage from that index's fresh inputs first. -/
theorem familyLaw_inverse {Result : Type} (assigns : FamilyAssignment)
    (injective : FamilyInjective assigns) (index : FixedKeyIndex) (value : Block)
    (fresh : value ∉ pinnedRange (assigns index))
    (continuation : Block → PermutationOracle FixedKeyIndex Block → PMF Result) :
    ((familyLaw assigns).bind fun oracle =>
        continuation ((oracle.permutation index).symm value) oracle) =
      (freshInputLaw (assigns index)).bind fun input =>
        (familyLaw (pinFamily assigns index input value)).bind fun oracle =>
          continuation input oracle := by
  have base : ((familyLaw assigns).bind fun oracle =>
        continuation ((oracle.permutation index).symm value) oracle) =
      (compatibleLaw (assigns index)).bind fun permutation =>
        (productPMF fun other => compatibleLaw (assigns other)).bind fun permutations =>
          continuation (((Function.update permutations index permutation) index).symm value)
            ⟨Function.update permutations index permutation⟩ :=
    (familyLaw_bind assigns _).trans (productPMF_bind_place _ index _)
  simp only [Function.update_self] at base
  rw [base, compatibleLaw_inverse (assigns index) (injective index) value fresh
    (fun answer permutation =>
      (productPMF fun other => compatibleLaw (assigns other)).bind fun permutations =>
        continuation answer ⟨Function.update permutations index permutation⟩)]
  refine congrArg (PMF.bind _) (funext fun input => ?_)
  have right : ((familyLaw (pinFamily assigns index input value)).bind fun oracle =>
        continuation input oracle) =
      (compatibleLaw (Function.update (assigns index) input (some value))).bind
        fun permutation =>
          (productPMF fun other => compatibleLaw (assigns other)).bind fun permutations =>
            continuation input ⟨Function.update permutations index permutation⟩ := by
    refine Eq.trans (familyLaw_bind _ _) ?_
    rw [familyLaw_laws_pinFamily assigns index input value]
    exact productPMF_bind_place_update _ index _ _
  exact right.symm

/-! ### The lazy family handler -/

/-- Replace the whole fixed-key permutation family of a state. -/
def setFamily (state : State) (oracle : PermutationOracle FixedKeyIndex Block) : State :=
  { state with view := (oracle, state.view.2) }

theorem setFamily_log (state : State) (oracle : PermutationOracle FixedKeyIndex Block) :
    (setFamily state oracle).log = state.log := rfl

theorem setFamily_logged (state : State) (oracle : PermutationOracle FixedKeyIndex Block)
    (request : Query) :
    { setFamily state oracle with log := request :: state.log } =
      setFamily { state with log := request :: state.log } oracle := rfl

theorem publicAnswer_setFamily_forward (state : State)
    (oracle : PermutationOracle FixedKeyIndex Block) (index : FixedKeyIndex) (domain : Block) :
    publicAnswer (setFamily state oracle).view (PublicQuery.fixedForward index domain) =
      oracle.permutation index domain := rfl

theorem publicAnswer_setFamily_inverse (state : State)
    (oracle : PermutationOracle FixedKeyIndex Block) (index : FixedKeyIndex) (range : Block) :
    publicAnswer (setFamily state oracle).view (PublicQuery.fixedInverse index range) =
      (oracle.permutation index).symm range := rfl

theorem publicAnswer_setFamily_encForward (state : State)
    (oracle : PermutationOracle FixedKeyIndex Block) (index : Garbling.EncIndex)
    (domain : Block) :
    publicAnswer (setFamily state oracle).view (PublicQuery.encForward index domain) =
      publicAnswer state.view (PublicQuery.encForward index domain) := rfl

theorem publicAnswer_setFamily_encInverse (state : State)
    (oracle : PermutationOracle FixedKeyIndex Block) (index : Garbling.EncIndex) (range : Block) :
    publicAnswer (setFamily state oracle).view (PublicQuery.encInverse index range) =
      publicAnswer state.view (PublicQuery.encInverse index range) := rfl

theorem publicAnswer_setFamily_hash (state : State)
    (oracle : PermutationOracle FixedKeyIndex Block) (point : BN254.BaseField) :
    publicAnswer (setFamily state oracle).view (PublicQuery.hash point) =
      publicAnswer state.view (PublicQuery.hash point) := rfl

/-- The lazy family handler: every fixed-key query is answered from the transcript of its
own index, extending it by a uniform choice among that index's free values when the query
is not yet pinned; every other query is answered from the view. -/
def lazyFamilyAnswer (view : View) :
    (request : Query) → FamilyAssignment → PMF (request.Answer × FamilyAssignment)
  | .fixedForward index domain, assigns =>
      ((assigns index) domain).elim
        ((freshValueLaw (assigns index)).map fun value =>
          (value, pinFamily assigns index domain value))
        (fun value => PMF.pure (value, assigns))
  | .fixedInverse index range, assigns =>
      (pinnedInput (assigns index) range).elim
        ((freshInputLaw (assigns index)).map fun domain =>
          (domain, pinFamily assigns index domain range))
        (fun domain => PMF.pure (domain, assigns))
  | .encForward index domain, assigns =>
      PMF.pure (view.2.1.permutation index domain, assigns)
  | .encInverse index range, assigns =>
      PMF.pure ((view.2.1.permutation index).symm range, assigns)
  | .hash point, assigns => PMF.pure (randomOracleAnswer view.2.2 point, assigns)

/-- The lazy family run: no permutation is ever sampled, only the transcripts. -/
def lazyFamilyRun {Result : Type} :
    {budget : Nat} →
      OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget →
        State → FamilyAssignment → PMF ((Result × List Query) × FamilyAssignment)
  | _, .pure distribution, state, assigns =>
      distribution.map fun value => ((value, state.log), assigns)
  | _, .query request next, state, assigns =>
      (lazyFamilyAnswer state.view request assigns).bind fun pair =>
        lazyFamilyRun (next pair.1) { state with log := request :: state.log } pair.2
  | _, .sample distribution next, state, assigns =>
      distribution.bind fun value => lazyFamilyRun (next value) state assigns

/-! ### The eager-to-lazy equivalence -/

/-- One query step of the family model. -/
theorem lazyFamily_query_step {Outcome : Type} (request : Query) (state : State)
    (assigns : FamilyAssignment) (injective : FamilyInjective assigns)
    (eager : (answer : request.Answer) → PermutationOracle FixedKeyIndex Block → PMF Outcome)
    (lazy : (answer : request.Answer) → FamilyAssignment → PMF Outcome)
    (step : ∀ (answer : request.Answer) (other : FamilyAssignment), FamilyInjective other →
      ((familyLaw other).bind fun oracle => eager answer oracle) = lazy answer other) :
    ((familyLaw assigns).bind fun oracle =>
        eager (publicAnswer (setFamily state oracle).view request) oracle) =
      (lazyFamilyAnswer state.view request assigns).bind fun pair => lazy pair.1 pair.2 := by
  cases request with
  | fixedForward index domain =>
    cases pinned : assigns index domain with
    | some value =>
      have lazyEq : lazyFamilyAnswer state.view (PublicQuery.fixedForward index domain) assigns =
          PMF.pure (value, assigns) := by
        simp only [lazyFamilyAnswer, pinned]
        rfl
      calc ((familyLaw assigns).bind fun oracle =>
            eager (publicAnswer (setFamily state oracle).view
              (PublicQuery.fixedForward index domain)) oracle)
          = (familyLaw assigns).bind (fun oracle => eager value oracle) := by
            refine bind_congr_support fun oracle member => ?_
            rw [publicAnswer_setFamily_forward,
              familyLaw_support assigns injective member index domain value pinned]
        _ = lazy value assigns := step value assigns injective
        _ = (lazyFamilyAnswer state.view (PublicQuery.fixedForward index domain) assigns).bind
              fun pair => lazy pair.1 pair.2 := by
            rw [lazyEq]
            exact (PMF.pure_bind (value, assigns) fun pair => lazy pair.1 pair.2).symm
    | none =>
      have lazyEq : lazyFamilyAnswer state.view (PublicQuery.fixedForward index domain) assigns =
          (freshValueLaw (assigns index)).map fun value =>
            (value, pinFamily assigns index domain value) := by
        simp only [lazyFamilyAnswer, pinned]
        rfl
      calc ((familyLaw assigns).bind fun oracle =>
            eager (publicAnswer (setFamily state oracle).view
              (PublicQuery.fixedForward index domain)) oracle)
          = (familyLaw assigns).bind (fun oracle =>
              eager (oracle.permutation index domain) oracle) := by
            refine congrArg (PMF.bind _) (funext fun oracle => ?_)
            rw [publicAnswer_setFamily_forward]
        _ = (freshValueLaw (assigns index)).bind (fun value =>
              (familyLaw (pinFamily assigns index domain value)).bind fun oracle =>
                eager value oracle) :=
            familyLaw_forward assigns injective index domain pinned eager
        _ = (freshValueLaw (assigns index)).bind (fun value =>
              lazy value (pinFamily assigns index domain value)) := by
            refine bind_congr_support fun value member => ?_
            exact step value (pinFamily assigns index domain value)
              (pinFamily_injective assigns injective index domain value
                (freshValueLaw_support (assigns index)
                  (unused_nonempty (assigns index) (injective index) domain pinned) member))
        _ = (lazyFamilyAnswer state.view (PublicQuery.fixedForward index domain) assigns).bind
              fun pair => lazy pair.1 pair.2 := by
            rw [lazyEq]
            exact (bind_of_map (freshValueLaw (assigns index))
              (fun value => (value, pinFamily assigns index domain value))
              fun pair => lazy pair.1 pair.2).symm
  | fixedInverse index range =>
    cases transposed : pinnedInput (assigns index) range with
    | some domain =>
      have pin := (pinnedInput_eq_some_iff (assigns index) (injective index) range domain).mp
        transposed
      have lazyEq : lazyFamilyAnswer state.view (PublicQuery.fixedInverse index range) assigns =
          PMF.pure (domain, assigns) := by
        simp only [lazyFamilyAnswer, transposed]
        rfl
      calc ((familyLaw assigns).bind fun oracle =>
            eager (publicAnswer (setFamily state oracle).view
              (PublicQuery.fixedInverse index range)) oracle)
          = (familyLaw assigns).bind (fun oracle => eager domain oracle) := by
            refine bind_congr_support fun oracle member => ?_
            rw [publicAnswer_setFamily_inverse,
              ← familyLaw_support assigns injective member index domain range pin,
              Equiv.symm_apply_apply]
        _ = lazy domain assigns := step domain assigns injective
        _ = (lazyFamilyAnswer state.view (PublicQuery.fixedInverse index range) assigns).bind
              fun pair => lazy pair.1 pair.2 := by
            rw [lazyEq]
            exact (PMF.pure_bind (domain, assigns) fun pair => lazy pair.1 pair.2).symm
    | none =>
      have fresh := notMem_pinnedRange_of_pinnedInput_eq_none (assigns index) (injective index)
        transposed
      have lazyEq : lazyFamilyAnswer state.view (PublicQuery.fixedInverse index range) assigns =
          (freshInputLaw (assigns index)).map fun domain =>
            (domain, pinFamily assigns index domain range) := by
        simp only [lazyFamilyAnswer, transposed]
        rfl
      calc ((familyLaw assigns).bind fun oracle =>
            eager (publicAnswer (setFamily state oracle).view
              (PublicQuery.fixedInverse index range)) oracle)
          = (familyLaw assigns).bind (fun oracle =>
              eager ((oracle.permutation index).symm range) oracle) := by
            refine congrArg (PMF.bind _) (funext fun oracle => ?_)
            rw [publicAnswer_setFamily_inverse]
        _ = (freshInputLaw (assigns index)).bind (fun domain =>
              (familyLaw (pinFamily assigns index domain range)).bind fun oracle =>
                eager domain oracle) :=
            familyLaw_inverse assigns injective index range fresh eager
        _ = (freshInputLaw (assigns index)).bind (fun domain =>
              lazy domain (pinFamily assigns index domain range)) := by
            refine bind_congr_support fun domain member => ?_
            exact step domain (pinFamily assigns index domain range)
              (pinFamily_injective assigns injective index domain range fresh)
        _ = (lazyFamilyAnswer state.view (PublicQuery.fixedInverse index range) assigns).bind
              fun pair => lazy pair.1 pair.2 := by
            rw [lazyEq]
            exact (bind_of_map (freshInputLaw (assigns index))
              (fun domain => (domain, pinFamily assigns index domain range))
              fun pair => lazy pair.1 pair.2).symm
  | encForward index domain =>
    calc ((familyLaw assigns).bind fun oracle =>
          eager (publicAnswer (setFamily state oracle).view
            (PublicQuery.encForward index domain)) oracle)
        = lazy (publicAnswer state.view (PublicQuery.encForward index domain)) assigns :=
          step (publicAnswer state.view (PublicQuery.encForward index domain)) assigns injective
      _ = (lazyFamilyAnswer state.view (PublicQuery.encForward index domain) assigns).bind
            fun pair => lazy pair.1 pair.2 :=
          (PMF.pure_bind (publicAnswer state.view (PublicQuery.encForward index domain), assigns)
            fun pair => lazy pair.1 pair.2).symm
  | encInverse index range =>
    calc ((familyLaw assigns).bind fun oracle =>
          eager (publicAnswer (setFamily state oracle).view
            (PublicQuery.encInverse index range)) oracle)
        = lazy (publicAnswer state.view (PublicQuery.encInverse index range)) assigns :=
          step (publicAnswer state.view (PublicQuery.encInverse index range)) assigns injective
      _ = (lazyFamilyAnswer state.view (PublicQuery.encInverse index range) assigns).bind
            fun pair => lazy pair.1 pair.2 :=
          (PMF.pure_bind (publicAnswer state.view (PublicQuery.encInverse index range), assigns)
            fun pair => lazy pair.1 pair.2).symm
  | hash point =>
    calc ((familyLaw assigns).bind fun oracle =>
          eager (publicAnswer (setFamily state oracle).view (PublicQuery.hash point)) oracle)
        = lazy (publicAnswer state.view (PublicQuery.hash point)) assigns :=
          step (publicAnswer state.view (PublicQuery.hash point)) assigns injective
      _ = (lazyFamilyAnswer state.view (PublicQuery.hash point) assigns).bind
            fun pair => lazy pair.1 pair.2 :=
          (PMF.pure_bind (publicAnswer state.view (PublicQuery.hash point), assigns)
            fun pair => lazy pair.1 pair.2).symm

/-- The eager family model and the lazy family model give the same law of the result, the
log and the whole permutation family: sampling the family before the run is the same as
sampling only its transcripts during the run and the family afterwards, conditioned on
those transcripts. -/
theorem familyLaw_run {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget) :
    ∀ (state : State) (assigns : FamilyAssignment), FamilyInjective assigns →
      ((familyLaw assigns).bind fun oracle =>
          (program.run idealOracle (setFamily state oracle)).map fun output =>
            ((output.1, output.2.log), oracle)) =
        (lazyFamilyRun program state assigns).bind fun output =>
          (familyLaw output.2).map fun oracle => (output.1, oracle) := by
  induction program with
  | pure distribution =>
    intro state assigns injective
    have lhs : ((familyLaw assigns).bind fun oracle =>
          ((OracleProgram.pure (oracle := publicOracleSpec FixedKeyIndex Garbling.EncIndex)
              (budget := budget) distribution).run idealOracle (setFamily state oracle)).map
            fun output => ((output.1, output.2.log), oracle)) =
        (familyLaw assigns).bind fun oracle =>
          distribution.bind fun value => PMF.pure ((value, state.log), oracle) := by
      refine congrArg (PMF.bind _) (funext fun oracle => ?_)
      rw [OracleProgram.run_pure, PMF.map, PMF.map, PMF.bind_bind]
      exact congrArg (PMF.bind _) (funext fun value => PMF.pure_bind _ _)
    have rhs : ((lazyFamilyRun (OracleProgram.pure (budget := budget) distribution) state
          assigns).bind fun output =>
            (familyLaw output.2).map fun oracle => (output.1, oracle)) =
        distribution.bind fun value => (familyLaw assigns).bind fun oracle =>
          PMF.pure ((value, state.log), oracle) := by
      show ((distribution.map fun value => ((value, state.log), assigns)).bind fun output =>
        (familyLaw output.2).map fun oracle => (output.1, oracle)) = _
      rw [bind_of_map]
      exact congrArg (PMF.bind _) (funext fun value => rfl)
    exact lhs.trans ((PMF.bind_comm _ _ _).trans rhs.symm)
  | query request next inductionHypothesis =>
    intro state assigns injective
    have lhs : ((familyLaw assigns).bind fun oracle =>
          ((OracleProgram.query request next).run idealOracle (setFamily state oracle)).map
            fun output => ((output.1, output.2.log), oracle)) =
        (familyLaw assigns).bind fun oracle =>
          ((next (publicAnswer (setFamily state oracle).view request)).run idealOracle
              (setFamily { state with log := request :: state.log } oracle)).map
            fun output => ((output.1, output.2.log), oracle) := by
      refine congrArg (PMF.bind _) (funext fun oracle => ?_)
      rw [OracleProgram.run_query]
      rfl
    have rhs : ((lazyFamilyRun (OracleProgram.query request next) state assigns).bind
          fun output => (familyLaw output.2).map fun oracle => (output.1, oracle)) =
        (lazyFamilyAnswer state.view request assigns).bind fun pair =>
          (lazyFamilyRun (next pair.1) { state with log := request :: state.log } pair.2).bind
            fun output => (familyLaw output.2).map fun oracle => (output.1, oracle) :=
      PMF.bind_bind _ _ _
    refine lhs.trans (Eq.trans ?_ rhs.symm)
    exact lazyFamily_query_step request state assigns injective
      (fun answer oracle => ((next answer).run idealOracle
        (setFamily { state with log := request :: state.log } oracle)).map
          fun output => ((output.1, output.2.log), oracle))
      (fun answer other => (lazyFamilyRun (next answer)
        { state with log := request :: state.log } other).bind fun output =>
          (familyLaw output.2).map fun oracle => (output.1, oracle))
      fun answer other injectiveOther =>
        inductionHypothesis answer { state with log := request :: state.log } other injectiveOther
  | sample distribution next inductionHypothesis =>
    intro state assigns injective
    have lhs : ((familyLaw assigns).bind fun oracle =>
          ((OracleProgram.sample distribution next).run idealOracle
            (setFamily state oracle)).map fun output =>
              ((output.1, output.2.log), oracle)) =
        (familyLaw assigns).bind fun oracle => distribution.bind fun value =>
          ((next value).run idealOracle (setFamily state oracle)).map
            fun output => ((output.1, output.2.log), oracle) := by
      refine congrArg (PMF.bind _) (funext fun oracle => ?_)
      rw [OracleProgram.run_sample, PMF.map_bind]
    have rhs : ((lazyFamilyRun (OracleProgram.sample distribution next) state assigns).bind
          fun output => (familyLaw output.2).map fun oracle => (output.1, oracle)) =
        distribution.bind fun value => (lazyFamilyRun (next value) state assigns).bind
          fun output => (familyLaw output.2).map fun oracle => (output.1, oracle) :=
      PMF.bind_bind _ _ _
    refine lhs.trans (Eq.trans ((PMF.bind_comm _ _ _).trans ?_) rhs.symm)
    exact congrArg (PMF.bind _)
      (funext fun value => inductionHypothesis value state assigns injective)

/-- The conditional form of a family run in the shape a game consumes: a uniform
permutation family before the run is the lazy transcripts during the run and the family law
afterwards. The initial transcripts are empty, so the injectivity hypothesis is discharged
and the uniform law is `familyLaw_empty`. -/
theorem uniform_run_familyLaw {Result Value : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget)
    (state : State)
    (continuation : Result × List Query → PermutationOracle FixedKeyIndex Block → PMF Value) :
    ((PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind fun oracle =>
        (program.run idealOracle (setFamily state oracle)).bind fun output =>
          continuation (output.1, output.2.log) oracle) =
      (lazyFamilyRun program state (fun _ _ => none)).bind fun output =>
        (familyLaw output.2).bind fun oracle => continuation output.1 oracle := by
  have empty : FamilyInjective (fun _ _ => none) := fun _ => emptyAssignment_injective
  have left : ((PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).bind
        fun oracle => (program.run idealOracle (setFamily state oracle)).bind fun output =>
          continuation (output.1, output.2.log) oracle) =
      ((familyLaw (fun _ _ => none)).bind fun oracle =>
          (program.run idealOracle (setFamily state oracle)).map fun output =>
            ((output.1, output.2.log), oracle)).bind fun pair =>
        continuation pair.1 pair.2 := by
    rw [familyLaw_empty, PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun oracle => ?_)
    rw [bind_of_map]
  rw [left, familyLaw_run program state (fun _ _ => none) empty, PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun output => ?_)
  rw [bind_of_map]

/-! ### The budget: one pin per query, summed over the indices -/

/-- The number of points the whole family of transcripts has pinned. A permutation query
names exactly one index, so this sum -- not the per-index count -- is what grows by one per
query, and it is what the steering hop's charge is stated against. -/
def familyPinnedCount (assigns : FamilyAssignment) : Nat :=
  ∑ index, pinnedCount (assigns index)

theorem familyPinnedCount_empty : familyPinnedCount (fun _ _ => none) = 0 := by
  rw [familyPinnedCount]
  exact Finset.sum_eq_zero fun index _ => pinnedCount_empty

/-- Pinning one point of one index raises the family count by at most one. -/
theorem familyPinnedCount_pinFamily_le (assigns : FamilyAssignment) (index : FixedKeyIndex)
    (input value : Block) :
    familyPinnedCount (pinFamily assigns index input value) ≤ familyPinnedCount assigns + 1 := by
  classical
  have pointwise : ∀ other ∈ Finset.univ,
      pinnedCount (pinFamily assigns index input value other) ≤
        pinnedCount (assigns other) + (if other = index then 1 else 0) := by
    intro other _
    by_cases same : other = index
    · subst same
      rw [pinFamily_self, if_pos rfl]
      exact pinnedCount_update_le (assigns other) input value
    · rw [pinFamily_of_ne assigns index other input value same, if_neg same]
      omega
  refine le_trans (Finset.sum_le_sum pointwise) ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ index fun _ => 1,
    if_pos (Finset.mem_univ index)]
  exact le_rfl

theorem lazyFamilyAnswer_pinnedCount (view : View) (request : Query)
    (assigns : FamilyAssignment) (pair : request.Answer × FamilyAssignment)
    (member : pair ∈ (lazyFamilyAnswer view request assigns).support) :
    familyPinnedCount pair.2 ≤ familyPinnedCount assigns + 1 := by
  cases request with
  | fixedForward index domain =>
    cases pinned : assigns index domain with
    | some value =>
      have lazyEq : lazyFamilyAnswer view (PublicQuery.fixedForward index domain) assigns =
          PMF.pure (value, assigns) := by
        simp only [lazyFamilyAnswer, pinned]
        rfl
      rw [lazyEq] at member
      rw [eq_of_mem_support_pure member]
      exact Nat.le_succ _
    | none =>
      have lazyEq : lazyFamilyAnswer view (PublicQuery.fixedForward index domain) assigns =
          (freshValueLaw (assigns index)).map fun value =>
            (value, pinFamily assigns index domain value) := by
        simp only [lazyFamilyAnswer, pinned]
        rfl
      rw [lazyEq] at member
      obtain ⟨value, equal⟩ := exists_of_mem_support_map member
      rw [← equal]
      exact familyPinnedCount_pinFamily_le assigns index domain value
  | fixedInverse index range =>
    cases transposed : pinnedInput (assigns index) range with
    | some domain =>
      have lazyEq : lazyFamilyAnswer view (PublicQuery.fixedInverse index range) assigns =
          PMF.pure (domain, assigns) := by
        simp only [lazyFamilyAnswer, transposed]
        rfl
      rw [lazyEq] at member
      rw [eq_of_mem_support_pure member]
      exact Nat.le_succ _
    | none =>
      have lazyEq : lazyFamilyAnswer view (PublicQuery.fixedInverse index range) assigns =
          (freshInputLaw (assigns index)).map fun domain =>
            (domain, pinFamily assigns index domain range) := by
        simp only [lazyFamilyAnswer, transposed]
        rfl
      rw [lazyEq] at member
      obtain ⟨domain, equal⟩ := exists_of_mem_support_map member
      rw [← equal]
      exact familyPinnedCount_pinFamily_le assigns index domain range
  | encForward index domain =>
    have lazyEq : lazyFamilyAnswer view (PublicQuery.encForward index domain) assigns =
        PMF.pure (publicAnswer view (PublicQuery.encForward index domain), assigns) := rfl
    rw [lazyEq] at member
    rw [eq_of_mem_support_pure member]
    exact Nat.le_succ _
  | encInverse index range =>
    have lazyEq : lazyFamilyAnswer view (PublicQuery.encInverse index range) assigns =
        PMF.pure (publicAnswer view (PublicQuery.encInverse index range), assigns) := rfl
    rw [lazyEq] at member
    rw [eq_of_mem_support_pure member]
    exact Nat.le_succ _
  | hash point =>
    have lazyEq : lazyFamilyAnswer view (PublicQuery.hash point) assigns =
        PMF.pure (publicAnswer view (PublicQuery.hash point), assigns) := rfl
    rw [lazyEq] at member
    rw [eq_of_mem_support_pure member]
    exact Nat.le_succ _

/-- A lazy family run of a program with `budget` queries pins at most `budget` further
points **in total over all indices**. This is the pointwise induction that replaces the
per-index accounting: a log entry pins only at its own index. -/
theorem lazyFamilyRun_pinnedCount {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget) :
    ∀ (state : State) (assigns : FamilyAssignment)
      (output : (Result × List Query) × FamilyAssignment),
      output ∈ (lazyFamilyRun program state assigns).support →
        familyPinnedCount output.2 ≤ familyPinnedCount assigns + budget := by
  induction program with
  | pure distribution =>
    intro state assigns output member
    rw [lazyFamilyRun, PMF.support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact Nat.le_add_right _ _
  | query request next inductionHypothesis =>
    intro state assigns output member
    rw [lazyFamilyRun, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨pair, pairMember, member⟩ := member
    have tail := inductionHypothesis pair.1 { state with log := request :: state.log } pair.2
      output member
    have head := lazyFamilyAnswer_pinnedCount state.view request assigns pair pairMember
    omega
  | sample distribution next inductionHypothesis =>
    intro state assigns output member
    rw [lazyFamilyRun, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨value, _, member⟩ := member
    exact inductionHypothesis value state assigns output member

/-! ### The transcripts cover the log -/

/-- Every index's transcript pins every tracked query the log records at that index. -/
def FamilyCovers (assigns : FamilyAssignment) (log : List Query) : Prop :=
  ∀ index, TranscriptCovers index (assigns index) log

theorem familyCovers_empty : FamilyCovers (fun _ _ => none) [] :=
  fun index => transcriptCovers_empty index

/-- One lazy family answer keeps every transcript injective and covering, and covers its
own query at its own index. -/
theorem lazyFamilyAnswer_covers (view : View) (request : Query) (assigns : FamilyAssignment)
    (injective : FamilyInjective assigns) (pair : request.Answer × FamilyAssignment)
    (member : pair ∈ (lazyFamilyAnswer view request assigns).support) (log : List Query)
    (covers : FamilyCovers assigns log) :
    FamilyInjective pair.2 ∧ FamilyCovers pair.2 (request :: log) := by
  cases request with
  | fixedForward index domain =>
    cases pinned : assigns index domain with
    | some value =>
      have lazyEq : lazyFamilyAnswer view (PublicQuery.fixedForward index domain) assigns =
          PMF.pure (value, assigns) := by
        simp only [lazyFamilyAnswer, pinned]
        rfl
      rw [lazyEq] at member
      have same : pair.2 = assigns := by rw [eq_of_mem_support_pure member]
      rw [same]
      refine ⟨injective, fun other => ⟨fun input logged => ?_, fun point logged => ?_⟩⟩
      · rcases List.mem_cons.mp logged with head | tail
        · have parts : other = index ∧ input = domain := by simpa using head
          rw [parts.1, parts.2]
          exact mem_pinnedDomain pinned
        · exact (covers other).1 input tail
      · rcases List.mem_cons.mp logged with head | tail
        · exact absurd head (by simp)
        · exact (covers other).2 point tail
    | none =>
      have lazyEq : lazyFamilyAnswer view (PublicQuery.fixedForward index domain) assigns =
          (freshValueLaw (assigns index)).map fun value =>
            (value, pinFamily assigns index domain value) := by
        simp only [lazyFamilyAnswer, pinned]
        rfl
      rw [lazyEq] at member
      obtain ⟨value, valueMember, equal⟩ := exists_mem_support_of_mem_support_map _ _ member
      have unusedNonempty := unused_nonempty (assigns index) (injective index) domain pinned
      have valueFresh : value ∉ pinnedRange (assigns index) :=
        freshValueLaw_support (assigns index) unusedNonempty valueMember
      have same : pair.2 = pinFamily assigns index domain value := by rw [← equal]
      rw [same]
      refine ⟨pinFamily_injective assigns injective index domain value valueFresh,
        fun other => ⟨fun input logged => ?_, fun point logged => ?_⟩⟩
      · by_cases atIndex : other = index
        · rw [atIndex, pinFamily_self, pinnedDomain_update]
          rcases List.mem_cons.mp logged with head | tail
          · have parts : other = index ∧ input = domain := by simpa using head
            exact Set.mem_insert_iff.mpr (Or.inl parts.2)
          · refine Set.mem_insert_of_mem _ ?_
            rw [← atIndex]
            exact (covers other).1 input tail
        · rw [pinFamily_of_ne assigns index other domain value atIndex]
          rcases List.mem_cons.mp logged with head | tail
          · have parts : other = index ∧ input = domain := by simpa using head
            exact absurd parts.1 atIndex
          · exact (covers other).1 input tail
      · by_cases atIndex : other = index
        · rw [atIndex, pinFamily_self]
          rcases List.mem_cons.mp logged with head | tail
          · exact absurd head (by simp)
          · refine pinnedRange_update_subset (assigns index) domain value pinned ?_
            rw [← atIndex]
            exact (covers other).2 point tail
        · rw [pinFamily_of_ne assigns index other domain value atIndex]
          rcases List.mem_cons.mp logged with head | tail
          · exact absurd head (by simp)
          · exact (covers other).2 point tail
  | fixedInverse index range =>
    cases transposed : pinnedInput (assigns index) range with
    | some domain =>
      have lazyEq : lazyFamilyAnswer view (PublicQuery.fixedInverse index range) assigns =
          PMF.pure (domain, assigns) := by
        simp only [lazyFamilyAnswer, transposed]
        rfl
      rw [lazyEq] at member
      have same : pair.2 = assigns := by rw [eq_of_mem_support_pure member]
      rw [same]
      refine ⟨injective, fun other => ⟨fun input logged => ?_, fun point logged => ?_⟩⟩
      · rcases List.mem_cons.mp logged with head | tail
        · exact absurd head (by simp)
        · exact (covers other).1 input tail
      · rcases List.mem_cons.mp logged with head | tail
        · have parts : other = index ∧ point = range := by simpa using head
          rw [parts.1, parts.2]
          exact mem_pinnedRange_of_pinnedInput (assigns index) range domain transposed
        · exact (covers other).2 point tail
    | none =>
      have rangeFresh : range ∉ pinnedRange (assigns index) :=
        notMem_pinnedRange_of_pinnedInput_eq_none (assigns index) (injective index) transposed
      have lazyEq : lazyFamilyAnswer view (PublicQuery.fixedInverse index range) assigns =
          (freshInputLaw (assigns index)).map fun domain =>
            (domain, pinFamily assigns index domain range) := by
        simp only [lazyFamilyAnswer, transposed]
        rfl
      rw [lazyEq] at member
      obtain ⟨domain, domainMember, equal⟩ := exists_mem_support_of_mem_support_map _ _ member
      have unpinnedNonempty :=
        unpinned_nonempty (assigns index) (injective index) range rangeFresh
      have freshDomain : assigns index domain = none :=
        freshInputLaw_support (assigns index) unpinnedNonempty domainMember
      have same : pair.2 = pinFamily assigns index domain range := by rw [← equal]
      rw [same]
      refine ⟨pinFamily_injective assigns injective index domain range rangeFresh,
        fun other => ⟨fun input logged => ?_, fun point logged => ?_⟩⟩
      · by_cases atIndex : other = index
        · rw [atIndex, pinFamily_self, pinnedDomain_update]
          rcases List.mem_cons.mp logged with head | tail
          · exact absurd head (by simp)
          · refine Set.mem_insert_of_mem _ ?_
            rw [← atIndex]
            exact (covers other).1 input tail
        · rw [pinFamily_of_ne assigns index other domain range atIndex]
          rcases List.mem_cons.mp logged with head | tail
          · exact absurd head (by simp)
          · exact (covers other).1 input tail
      · by_cases atIndex : other = index
        · rw [atIndex, pinFamily_self]
          rcases List.mem_cons.mp logged with head | tail
          · have parts : other = index ∧ point = range := by simpa using head
            refine ⟨domain, ?_⟩
            rw [Function.update_self, parts.2]
          · refine pinnedRange_update_subset (assigns index) domain range freshDomain ?_
            rw [← atIndex]
            exact (covers other).2 point tail
        · rw [pinFamily_of_ne assigns index other domain range atIndex]
          rcases List.mem_cons.mp logged with head | tail
          · have parts : other = index ∧ point = range := by simpa using head
            exact absurd parts.1 atIndex
          · exact (covers other).2 point tail
  | encForward index domain =>
    have lazyEq : lazyFamilyAnswer view (PublicQuery.encForward index domain) assigns =
        PMF.pure (publicAnswer view (PublicQuery.encForward index domain), assigns) := rfl
    rw [lazyEq] at member
    have same : pair.2 = assigns := by rw [eq_of_mem_support_pure member]
    rw [same]
    refine ⟨injective, fun other => ⟨fun input logged => ?_, fun point logged => ?_⟩⟩
    · rcases List.mem_cons.mp logged with head | tail
      · exact absurd head (by simp)
      · exact (covers other).1 input tail
    · rcases List.mem_cons.mp logged with head | tail
      · exact absurd head (by simp)
      · exact (covers other).2 point tail
  | encInverse index range =>
    have lazyEq : lazyFamilyAnswer view (PublicQuery.encInverse index range) assigns =
        PMF.pure (publicAnswer view (PublicQuery.encInverse index range), assigns) := rfl
    rw [lazyEq] at member
    have same : pair.2 = assigns := by rw [eq_of_mem_support_pure member]
    rw [same]
    refine ⟨injective, fun other => ⟨fun input logged => ?_, fun point logged => ?_⟩⟩
    · rcases List.mem_cons.mp logged with head | tail
      · exact absurd head (by simp)
      · exact (covers other).1 input tail
    · rcases List.mem_cons.mp logged with head | tail
      · exact absurd head (by simp)
      · exact (covers other).2 point tail
  | hash point =>
    have lazyEq : lazyFamilyAnswer view (PublicQuery.hash point) assigns =
        PMF.pure (publicAnswer view (PublicQuery.hash point), assigns) := rfl
    rw [lazyEq] at member
    have same : pair.2 = assigns := by rw [eq_of_mem_support_pure member]
    rw [same]
    refine ⟨injective, fun other => ⟨fun input logged => ?_, fun value logged => ?_⟩⟩
    · rcases List.mem_cons.mp logged with head | tail
      · exact absurd head (by simp)
      · exact (covers other).1 input tail
    · rcases List.mem_cons.mp logged with head | tail
      · exact absurd head (by simp)
      · exact (covers other).2 value tail


/-- A lazy family run pins every tracked query its log records, at that query's own index,
and keeps every transcript injective. -/
theorem lazyFamilyRun_covers {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedKeyIndex Garbling.EncIndex) Result budget) :
    ∀ (state : State) (assigns : FamilyAssignment), FamilyInjective assigns →
      FamilyCovers assigns state.log →
        ∀ output ∈ (lazyFamilyRun program state assigns).support,
          FamilyInjective output.2 ∧ FamilyCovers output.2 output.1.2 := by
  induction program with
  | pure distribution =>
    intro state assigns injective covers output member
    rw [lazyFamilyRun, PMF.support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact ⟨injective, covers⟩
  | query request next inductionHypothesis =>
    intro state assigns injective covers output member
    rw [lazyFamilyRun, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨pair, pairMember, member⟩ := member
    obtain ⟨stepInjective, stepCovers⟩ := lazyFamilyAnswer_covers state.view request assigns
      injective pair pairMember state.log covers
    exact inductionHypothesis pair.1 { state with log := request :: state.log } pair.2
      stepInjective stepCovers output member
  | sample distribution next inductionHypothesis =>
    intro state assigns injective covers output member
    rw [lazyFamilyRun, PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨value, _, member⟩ := member
    exact inductionHypothesis value state assigns injective covers output member

/-! ### The double programming, coordinatewise -/

/-- One index's share of a partial programming. -/
def programSlot (programs : Programs) (index : FixedKeyIndex) (permutation : Equiv Block Block) :
    Equiv Block Block :=
  match programs index with
  | none => permutation
  | some (label, range) => programmed permutation label range

theorem programIndices_eq_programSlot (programs : Programs)
    (oracle : PermutationOracle FixedKeyIndex Block) :
    programIndices programs oracle =
      ⟨fun index => programSlot programs index (oracle.permutation index)⟩ := rfl

/-- Programming the whole family twice -- honestly and then at the steering slots -- is, in
law, programming it once to the steered ranges.

This is the one-hop form the steering hop needs: the transcripts of the indices the steering
touches leave the selected label unpinned and have used neither range, and then the doubly
programmed family and the singly programmed one are the **same law**. The proof is
`compatibleLaw_double` at each touched index, carried across the product by
`productPMF_bind_pointwise`; the untouched indices need nothing, because both sides program
them identically. -/
theorem familyLaw_double {Result : Type} (assigns : FamilyAssignment)
    (injective : FamilyInjective assigns) (honest steered combined : Programs)
    (untouched : ∀ index, steered index = none → combined index = honest index)
    (covered : ∀ index label range, steered index = some (label, range) →
      ∃ other, honest index = some (label, other))
    (retargeted : ∀ index label range, steered index = some (label, range) →
      combined index = some (label, range))
    (good : ∀ index label first second, honest index = some (label, first) →
      steered index = some (label, second) →
      assigns index label = none ∧ first ∉ pinnedRange (assigns index) ∧
        second ∉ pinnedRange (assigns index))
    (continuation : PermutationOracle FixedKeyIndex Block → PMF Result) :
    ((familyLaw assigns).bind fun oracle =>
        continuation (programIndices steered (programIndices honest oracle))) =
      (familyLaw assigns).bind fun oracle =>
        continuation (programIndices combined oracle) := by
  have pointwise : ∀ (place : FixedKeyIndex) (cont : Equiv Block Block → PMF Result),
      ((compatibleLaw (assigns place)).bind fun permutation =>
          cont (programSlot steered place (programSlot honest place permutation))) =
        (compatibleLaw (assigns place)).bind fun permutation =>
          cont (programSlot combined place permutation) := by
    intro place cont
    cases steeredAt : steered place with
    | none =>
      have transform : ∀ permutation : Equiv Block Block,
          programSlot steered place (programSlot honest place permutation) =
            programSlot combined place permutation := by
        intro permutation
        rw [programSlot, steeredAt, programSlot, programSlot, untouched place steeredAt]
      exact congrArg (PMF.bind _) (funext fun permutation => by rw [transform permutation])
    | some pair =>
      obtain ⟨label, second⟩ := pair
      obtain ⟨first, honestAt⟩ := covered place label second steeredAt
      obtain ⟨labelFresh, firstUnused, secondUnused⟩ :=
        good place label first second honestAt steeredAt
      have doubled : ∀ permutation : Equiv Block Block,
          programSlot steered place (programSlot honest place permutation) =
            programmed (programmed permutation label first) label second := by
        intro permutation
        rw [programSlot, steeredAt, programSlot, honestAt]
      have single : ∀ permutation : Equiv Block Block,
          programSlot combined place permutation = programmed permutation label second := by
        intro permutation
        rw [programSlot, retargeted place label second steeredAt]
      rw [congrArg (PMF.bind _) (funext fun permutation => congrArg cont (doubled permutation)),
        congrArg (PMF.bind _) (funext fun permutation => congrArg cont (single permutation))]
      exact compatibleLaw_double (assigns place) (injective place) label first second
        labelFresh firstUnused secondUnused cont
  have left : ((familyLaw assigns).bind fun oracle =>
        continuation (programIndices steered (programIndices honest oracle))) =
      (productPMF fun index => compatibleLaw (assigns index)).bind fun permutations =>
        continuation ⟨fun index =>
          programSlot steered index (programSlot honest index (permutations index))⟩ :=
    familyLaw_bind assigns _
  have right : ((familyLaw assigns).bind fun oracle =>
        continuation (programIndices combined oracle)) =
      (productPMF fun index => compatibleLaw (assigns index)).bind fun permutations =>
        continuation ⟨fun index => programSlot combined index (permutations index)⟩ :=
    familyLaw_bind assigns _
  rw [left, right]
  exact productPMF_bind_pointwise _
    (fun index permutation => programSlot steered index (programSlot honest index permutation))
    (fun index permutation => programSlot combined index permutation)
    (fun permutations => continuation ⟨permutations⟩) pointwise

/-! ### The charge of the transcript conditions, over the whole family -/

/-- The chunk a slot reads: the programmed range with the label removed. -/
def slotChunk (slot : FixedKeySlot) (hash : BitVec 384) (pad : BitAdaptor.Ciphertext) : Block :=
  match slot with
  | .hash chunk => hash.extractLsb' (128 * chunk.val) 128
  | .pad chunk => pad.extractLsb' (128 * chunk.val) 128

/-- Every programmed range is its chunk exclusive-ored with the label. -/
theorem slotRange_eq_slotChunk (slot : FixedKeySlot) (hash : BitVec 384)
    (pad : BitAdaptor.Ciphertext) (label : Block) :
    slotRange slot hash pad label = slotChunk slot hash pad ^^^ label := by
  cases slot with
  | hash chunk => rfl
  | pad chunk => rfl

/-- The label values at which some index's transcript blocks the double programming: the
inputs that index has pinned, and, for each of its two chunk values, the label that would
put one of its pinned values at a programmed range.

The union runs over all indices, but only the indices the steering actually programs
contribute, and the sum of their pinned counts is `familyPinnedCount` -- which is what
`lazyFamilyRun_pinnedCount` bounds by the first stage's budget. This is exactly the
accounting the single-index tool could not see: it would have charged `familyPinnedCount`
once per programmed index. -/
def familyLabelHidden (assigns : FamilyAssignment)
    (honestChunk steeredChunk : FixedKeyIndex → Block) : Finset Block :=
  Finset.univ.biUnion fun index =>
    transcriptHidden (assigns index) (honestChunk index) (steeredChunk index)

/-- A family of transcripts pinning `k` points in total blocks at most `3 k` labels. -/
theorem familyLabelHidden_card (assigns : FamilyAssignment)
    (injective : FamilyInjective assigns) (honestChunk steeredChunk : FixedKeyIndex → Block) :
    (familyLabelHidden assigns honestChunk steeredChunk).card ≤
      3 * familyPinnedCount assigns := by
  refine le_trans (Finset.card_biUnion_le) ?_
  refine le_trans (Finset.sum_le_sum fun index _ =>
    transcriptHidden_card (assigns index) (injective index) (honestChunk index)
      (steeredChunk index)) ?_
  rw [familyPinnedCount, Finset.mul_sum]

set_option maxRecDepth 8000 in
/-- The charge of the steering hop, in one hop over the whole family: the selected label is
a uniform block the first stage never reads, so it blocks the double programming at some
index with mass at most three times the **total** number of points the first stage
pinned. -/
theorem uniform_keyLabel_familyHidden_le (assigns : FamilyAssignment)
    (injective : FamilyInjective assigns) (budget : Nat)
    (small : familyPinnedCount assigns ≤ budget)
    (honestChunk steeredChunk : FixedKeyIndex → Block) (coordinate : Bool)
    (position : Fin coordinateBitCount) (value : Bool) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
        {key | ∃ index : FixedKeyIndex,
          keyLabel key coordinate position value ∈ pinnedDomain (assigns index) ∨
            honestChunk index ^^^ keyLabel key coordinate position value ∈
              pinnedRange (assigns index) ∨
            steeredChunk index ^^^ keyLabel key coordinate position value ∈
              pinnedRange (assigns index)} ≤
      3 * budget / 2 ^ 128 := by
  have subset : {key : InputMacKey | ∃ index : FixedKeyIndex,
        keyLabel key coordinate position value ∈ pinnedDomain (assigns index) ∨
          honestChunk index ^^^ keyLabel key coordinate position value ∈
            pinnedRange (assigns index) ∨
          steeredChunk index ^^^ keyLabel key coordinate position value ∈
            pinnedRange (assigns index)} ⊆
      {key | keyLabel key coordinate position value ∈
        familyLabelHidden assigns honestChunk steeredChunk} := fun key member => by
    obtain ⟨index, blocked⟩ := member
    exact Finset.mem_biUnion.mpr ⟨index, Finset.mem_univ index,
      mem_transcriptHidden (assigns index) (honestChunk index) (steeredChunk index) _ blocked⟩
  refine le_trans (MeasureTheory.measure_mono subset) ?_
  rw [uniform_keyLabel_mem coordinate position value]
  have cast : ((3 * budget : Nat) : ENNReal) = 3 * (budget : ENNReal) := by push_cast; ring
  rw [← cast]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  exact le_trans (familyLabelHidden_card assigns injective honestChunk steeredChunk)
    (Nat.mul_le_mul_left 3 small)

/-- The bad event of the steering hop: at some index the steering reprograms, the
transcript of that index has already queried the selected label or already used one of the
two ranges. Its negation is exactly the `good` hypothesis of `familyLaw_double`. -/
def steeringBlocked (assigns : FamilyAssignment) (honest steered : Programs) : Prop :=
  ∃ index label first second, honest index = some (label, first) ∧
    steered index = some (label, second) ∧
    (label ∈ pinnedDomain (assigns index) ∨ first ∈ pinnedRange (assigns index) ∨
      second ∈ pinnedRange (assigns index))

/-- The `good` hypothesis of `familyLaw_double`, from the negation of the bad event. -/
theorem good_of_not_steeringBlocked (assigns : FamilyAssignment) (honest steered : Programs)
    (good : ¬ steeringBlocked assigns honest steered) :
    ∀ index label first second, honest index = some (label, first) →
      steered index = some (label, second) →
      assigns index label = none ∧ first ∉ pinnedRange (assigns index) ∧
        second ∉ pinnedRange (assigns index) := by
  intro index label first second honestAt steeredAt
  refine ⟨?_, fun used => good ⟨index, label, first, second, honestAt, steeredAt, Or.inr
      (Or.inl used)⟩,
    fun used => good ⟨index, label, first, second, honestAt, steeredAt, Or.inr (Or.inr used)⟩⟩
  cases pinned : assigns index label with
  | none => rfl
  | some value =>
    exact absurd ⟨index, label, first, second, honestAt, steeredAt,
      Or.inl (mem_pinnedDomain pinned)⟩ good

/-- The bad event is a condition on the selected label alone: both programmed ranges are
their chunk exclusive-ored with the label, so each of the three clauses names one label
value per pinned point. -/
theorem mem_familyLabelHidden_of_blocked (assigns : FamilyAssignment)
    (honest steered : Programs) (label : Block)
    (honestChunk steeredChunk : FixedKeyIndex → Block)
    (steeredLabel : ∀ index other second, steered index = some (other, second) → other = label)
    (honestForm : ∀ index first, honest index = some (label, first) →
      first = honestChunk index ^^^ label)
    (steeredForm : ∀ index second, steered index = some (label, second) →
      second = steeredChunk index ^^^ label)
    (blocked : steeringBlocked assigns honest steered) :
    ∃ index : FixedKeyIndex, label ∈ pinnedDomain (assigns index) ∨
      honestChunk index ^^^ label ∈ pinnedRange (assigns index) ∨
      steeredChunk index ^^^ label ∈ pinnedRange (assigns index) := by
  obtain ⟨index, other, first, second, honestAt, steeredAt, hit⟩ := blocked
  have otherEq : other = label := steeredLabel index other second steeredAt
  subst otherEq
  refine ⟨index, ?_⟩
  rcases hit with pinned | usedFirst | usedSecond
  · exact Or.inl pinned
  · exact Or.inr (Or.inl (honestForm index first honestAt ▸ usedFirst))
  · exact Or.inr (Or.inr (steeredForm index second steeredAt ▸ usedSecond))

end

end Kriterion.ArgoMAC.Security
