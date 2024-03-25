import ProperAction.ProperMaps
import Mathlib.Topology.Algebra.Group.Basic

class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  isProperMap_shear : IsProperMap (fun ⟨g, x⟩ ↦ ⟨g +ᵥ x, x⟩ : G × X → X × X)

@[to_additive]
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  isProperMap_shear : IsProperMap (fun ⟨g, x⟩ ↦ ⟨g • x, x⟩ : G × X → X × X)

variable {G X : Type*} [TopologicalSpace G] [TopologicalSpace X] [Group G] [MulAction G X]

-- Some things to generalize
#check t2Space_of_properlyDiscontinuousSMul_of_t2Space
#check Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite
