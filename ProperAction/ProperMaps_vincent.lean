import Mathlib.Topology.ProperMap
import Mathlib.Topology.Basic


/-!
## Missing facts about proper maps
-/

-- Teach `continuity` that proper maps are continuous (by definition...)
attribute [continuity] IsProperMap.continuous

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]


lemma comp_cont_is_cont (f:X→Y ) (g:Y → Z) (cf: Continuous f)(cg: Continuous g) :
    (Continuous (g∘f) ) := by
  -- faire apply? et selectionner:
  -- exact Continuous.comp cg cf

  -- unfold Continuous ne marche pas parce que c'est pas une def c'est une structure (a 1 seul champ)
  -- regarder apres la def les theoremes de base
  rw [continuous_def] -- re-ecrire le but en tuilisant le theoreme qui caracterise la continuite
  intro S hS
  -- moogle.ai: rechehce preimage composition pour trouver (f∘ g)⁻¹
  rw [Set.preimage_comp]
  rw [continuous_def] at cf cg -- on peut utiliser * pour substituer partout
  -- plus rapide que les specialize: partir du but
  -- apply cf
  -- apply cg

  specialize cg S hS
  specialize cf (g⁻¹' S) cg
  assumption



lemma IsProperMap.comp {f : X → Y} {g : Y → Z} (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (g ∘ f) := by
  rw [isProperMap_iff_clusterPt] at *
  constructor
  · apply Continuous.comp hg.1 hf.1
  · rcases hf with ⟨ cf , Ff ⟩
    rcases hg with ⟨ cg , Fg ⟩
    intro F z Hz
    set F2:= Filter.map f F
    -- syntaxe equivalente
    -- set F2:= F.map f
    rw [MapClusterPt] at Hz
    rw [← Filter.map_map] at Hz
    specialize Fg Hz
    rcases Fg with ⟨ y, hy1, hy2 ⟩
    specialize Ff hy2
    rcases Ff with ⟨ x, hx1, hx2 ⟩
    use x
    constructor
    · simp
      rw [hx1]
      assumption
    · assumption
