import Mathlib.Topology.ProperMap

/-!
## Missing facts about proper maps
-/

-- Teach `continuity` that proper maps are continuous (by definition...)
attribute [continuity] IsProperMap.continuous

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma IsProperMap.comp {f : X → Y} {g : Y → Z} (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (g ∘ f) := by
    constructor
    apply Continuous.comp hg.continuous hf.continuous
    intro F z h
    have ⟨y, hy1, hy2⟩ : ∃ y : Y, g y = z ∧ ClusterPt y (F.map f) := hg.clusterPt_of_mapClusterPt h
    have ⟨x, hx1, hx2⟩ : ∃ x : X, f x = y ∧ ClusterPt x F := hf.clusterPt_of_mapClusterPt hy2
    use x
    constructor
    rw [← hy1, ← hx1]
    rfl
    assumption
