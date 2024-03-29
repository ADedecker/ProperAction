import Mathlib.Topology.ProperMap

open Filter Set
/-!
## Missing facts about proper maps
-/

-- Teach `continuity` that proper maps are continuous (by definition...)
attribute [continuity] IsProperMap.continuous

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {f : X → Y} {g : Y → Z}

/-- The composition of two proper maps is proper. -/
lemma IsProperMap.comp (hf : IsProperMap f) (hg : IsProperMap g) :
  IsProperMap (g ∘ f) := by
  refine ⟨by continuity, fun ℱ z h ↦ ?_⟩
  rw [MapClusterPt, ← Filter.map_map] at h
  rcases hg.clusterPt_of_mapClusterPt h with ⟨y, hy1, hy2⟩
  rcases hf.clusterPt_of_mapClusterPt hy2 with ⟨x, hx1, hx2⟩
  use x
  rw [← hy1, ← hx1]
  exact ⟨rfl, by assumption⟩

/-- If the composition of two continuous functions `g ∘ f` is proper and `f` is surjective,
then `g` is proper. -/
lemma isProperMap_of_comp_of_surj {f : X → Y} {g : Y → Z} (hf : Continuous f)
    (hg : Continuous g) (hgf : IsProperMap (g ∘ f)) (f_surj : f.Surjective) : IsProperMap g := by
  refine ⟨hg, fun ℱ z h ↦ ?_⟩
  rcases hgf with ⟨_, h'⟩
  rw [← inf_top_eq ℱ, ← Filter.principal_univ, ← f_surj.range_eq, ← ℱ.map_comap f, MapClusterPt,
    Filter.map_map, ← MapClusterPt] at h
  rcases h' h with ⟨x, hx1, hx2⟩
  use f x
  refine ⟨hx1, ?_⟩
  apply neBot_of_comap
  apply NeBot.mono hx2
  calc
    nhds x ⊓ comap f ℱ
      ≤ comap f (nhds (f x)) ⊓ comap f ℱ := inf_le_inf_right (comap f ℱ) (hf.tendsto x).le_comap
    _ = comap f (nhds (f x) ⊓ ℱ) := by rw [← comap_inf]

/-- If the composition of two continuous functions `g ∘ f` is proper and `g` is injective,
then `f` is proper. -/
lemma isProperMap_of_comp_of_inj {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g)
    (hgf : IsProperMap (g ∘ f)) (g_inj : g.Injective) : IsProperMap f := by
  refine ⟨hf, fun ℱ y h ↦ ?_⟩
  rcases hgf with ⟨_, h'⟩
  have : MapClusterPt (g y) ℱ (g ∘ f) := by
    apply ClusterPt.map h
    exact hg.tendsto y
    rw [← map_map, Tendsto]
  rcases h' this with ⟨x, hx1, hx2⟩
  exact ⟨x, g_inj hx1, hx2⟩

/-- If the composition of two continuous functions `f : X → Y` and `g : Y → Z` is proper
and `Y` is T2, then `f` is proper. -/
lemma isProperMap_of_comp_of_t2 [T2Space Y] (hf : Continuous f) (hg : Continuous g)
    (hgf : IsProperMap (g ∘ f)) : IsProperMap f := by
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨hf, fun 𝒰 y h ↦ ?_⟩
  rw [isProperMap_iff_ultrafilter] at hgf
  rcases hgf with ⟨_, h'⟩
  have : Tendsto (g ∘ f) ↑𝒰 (nhds (g y)) := by
    rw [Tendsto, ← map_map]
    calc
      map g (map f ↑𝒰) ≤ map g (nhds y) := map_mono h
      _                ≤ nhds (g y) := hg.tendsto y
  rcases h' this with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

/-- An injective and continuous function is proper if and only if it is close. -/
lemma isProperMap_iff_isClosedMap_of_inj (f_cont : Continuous f) (f_inj : f.Injective) :
    IsProperMap f ↔ IsClosedMap f := by
  constructor
  exact fun h ↦ h.isClosedMap
  intro h
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨f_cont, h, ?_⟩
  intro y
  apply Set.Subsingleton.isCompact
  apply Set.Subsingleton.preimage subsingleton_singleton f_inj

/-- A injective continuous and closed map is proper. -/
lemma isProperMap_of_isClosedMap_of_inj (f_cont : Continuous f) (f_inj : f.Injective)
    (f_closed : IsClosedMap f) : IsProperMap f :=
  (isProperMap_iff_isClosedMap_of_inj f_cont f_inj).2 f_closed

/-- The coercion from a closed subset is proper. -/
lemma isProperMap_subtype_val_of_closed {U : Set X} (hU : IsClosed U) : IsProperMap ((↑) : U → X) :=
  isProperMap_of_isClosedMap_of_inj continuous_subtype_val Subtype.val_injective
  hU.closedEmbedding_subtype_val.isClosedMap

/-- The restriction of a proper map to a closed subset is proper. -/
lemma isProperMap_restr_of_proper_of_closed {U : Set X} (hf : IsProperMap f) (hU : IsClosed U) :
    IsProperMap (fun x : U ↦ f x) :=
  IsProperMap.comp (isProperMap_subtype_val_of_closed hU) hf

/-- A closed embedding is proper. -/
lemma isProperMap_of_closedEmbedding (hf : ClosedEmbedding f) : IsProperMap f :=
  isProperMap_of_isClosedMap_of_inj hf.continuous hf.inj hf.isClosedMap

/-- The range of a proper map is closed. -/
lemma IsProperMap.closed_range (hf : IsProperMap f) : IsClosed (range f) :=
  hf.isClosedMap.closed_range
