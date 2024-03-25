import Mathlib.Topology.ProperMap

/-!
## Missing facts about proper maps
-/

-- Teach `continuity` that proper maps are continuous (by definition...)
attribute [continuity] IsProperMap.continuous

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma IsProperMap.comp {f : X → Y} {g : Y → Z} (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (g ∘ f) := by
  sorry
