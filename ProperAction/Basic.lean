import ProperAction.ProperMaps
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.PUnitInstances

/-!
# Proper group actions
-/

set_option autoImplicit false

@[mk_iff]
class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  isProperMap_vadd_pair' : IsProperMap (fun gx ↦ ⟨gx.1 +ᵥ gx.2, gx.2⟩ : G × X → X × X)
-- isProperMap_vadd_pair' : IsProperMap (fun (g, x) ↦ ⟨g +ᵥ x, x⟩ : G × X → X × X)

@[to_additive, mk_iff]
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  isProperMap_smul_pair' : IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X)
-- isProperMap_smul_pair' : IsProperMap (fun (g, x) ↦ ⟨g • x, x⟩ : G × X → X × X)

@[to_additive]
lemma isProperMap_smul_pair (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace G] [TopologicalSpace X] [ProperSMul G X] :
    IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) :=
  ProperSMul.isProperMap_smul_pair'

#check properSMul_iff
#check properVAdd_iff

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]

@[to_additive]
instance [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := (isProperMap_smul_pair G X).continuous.fst

/-!
### Some typical cases of proper actions
-/

instance [ProperSMul G X] [ProperSMul G Y] : ProperSMul G (X × Y) where
  isProperMap_smul_pair' := sorry

instance {ι : Type*} {X : ι → Type*} [Π i, TopologicalSpace (X i)] [Π i, MulAction G (X i)]
    [∀ i, ProperSMul G (X i)] : ProperSMul G (Π i, X i) where
  isProperMap_smul_pair' := sorry

instance {H : Subgroup G} [ProperSMul G X] [IsClosed (H : Set G)] : ProperSMul H X where
  isProperMap_smul_pair' := sorry

-- for the one above, we may want to use this, or some variation of it:
example {H : Type*} [Group H] [MulAction H X] [TopologicalSpace H] [ProperSMul G X]
    (f : H →* G) (f_clemb : ClosedEmbedding f) (f_compat : ∀ (h : H) (x : X), f h • x = h • x) :
    ProperSMul H X where
  isProperMap_smul_pair' := sorry

-- Some things to generalize
#check t2Space_of_properlyDiscontinuousSMul_of_t2Space
#check Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite
