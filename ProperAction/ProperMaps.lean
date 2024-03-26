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
    rw [MapClusterPt, ← Filter.map_map] at h
    rcases hg.clusterPt_of_mapClusterPt h with ⟨y, hy1, hy2⟩
    rcases hf.clusterPt_of_mapClusterPt hy2 with ⟨x, hx1, hx2⟩
    use x
    constructor
    rw [← hy1, ← hx1]
    rfl
    assumption

lemma isProperMap_of_surj_isProperComp {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) (hgf : IsProperMap (g ∘ f)) (f_surj : f.Surjective) : IsProperMap g := by
  constructor
  assumption
  intro G z h
  have : MapClusterPt z (G.comap f) (g ∘ f) := by
    rw [MapClusterPt, ← Filter.map_map, Filter.map_comap, f_surj.range_eq]
    simpa
  rcases hgf.clusterPt_of_mapClusterPt this with ⟨x, hx1, hx2⟩
  use f x
  constructor
  rw [← hx1]
  rfl
  sorry
