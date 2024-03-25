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
    apply hg.continuous.comp hf.continuous
    intro F z h
    have ⟨y, hy1, hy2⟩ : ∃ y : Y, g y = z ∧ ClusterPt y (F.map f) := hg.clusterPt_of_mapClusterPt h
    rcases hf.clusterPt_of_mapClusterPt hy2 with ⟨x, hx1, hx2⟩
    use x
    constructor
    rw [← hy1, ← hx1]
    rfl
    assumption
