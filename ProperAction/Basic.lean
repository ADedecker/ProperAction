import ProperAction.ProperMaps
import Mathlib.GroupTheory.Subgroup.Actions
import Mathlib.Topology.Algebra.MulAction

/-!
# Proper group actions
-/

set_option autoImplicit false

/-- A group `G` equipped with a topology acts properly on a topological space `X` if the map
`(g, x) ↦ (g +ᵥ x, x)` is proper. -/
@[mk_iff]
class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  isProperMap_vadd_pair' : IsProperMap (fun gx ↦ ⟨gx.1 +ᵥ gx.2, gx.2⟩ : G × X → X × X)

/-- A group `G` equipped with a topology acts properly on a topological space `X` if the map
`(g, x) ↦ (g • x, x)` is proper. -/
@[to_additive, mk_iff]
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  isProperMap_smul_pair' : IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X)

attribute [to_additive existing] properSMul_iff

/-- A group `G` equipped with a topology acts properly on a topological space `X` if the map
`(g, x) ↦ (g • x, x)` is proper. -/
@[to_additive "A group `G` equipped with a topology acts properly on a topological space `X` if
the map `(g, x) ↦ (g +ᵥ x, x)` is proper."]
lemma isProperMap_smul_pair (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace G] [TopologicalSpace X] [ProperSMul G X] :
    IsProperMap (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) :=
  ProperSMul.isProperMap_smul_pair'

#check properSMul_iff
#check properVAdd_iff

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]

/-- If a group acts properly on a topological space, then the action is continuous by definition. -/
@[to_additive "If a group acts properly on a topological space, then the action is continuous
by definition."]
instance [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := (isProperMap_smul_pair G X).continuous.fst

/-!
### Some typical cases of proper actions
-/

instance [ProperSMul G X] [ContinuousSMul G Y] : ProperSMul G (X × Y) where
  isProperMap_smul_pair' := sorry

open Filter Topology Set

/-- A group acts `G` properly on a topological space `X` if and only if for all ultrafilters
`𝒰` on `X`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `g • x₂ = x₁` and `𝒰.fst` converges to `g`. -/
@[to_additive "A group acts `G` properly on a topological space `X` if and only if
for all ultrafilters `𝒰` on `X`, if `𝒰` converges to `(x₁, x₂)`
along the map `(g, x) ↦ (g • x, x)`, then there exists `g : G` such that `g • x₂ = x₁`
and `𝒰.fst` converges to `g`."]
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto : ProperSMul G X ↔ ContinuousSMul G X
    ∧ (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) 𝒰 (𝓝 (x₁, x₂)) →
    ∃ g : G, g • x₂ = x₁ ∧ Tendsto Prod.fst (𝒰 : Filter (G × X)) (𝓝 g)) := by
  constructor
  · intro h
    refine ⟨by infer_instance, fun 𝒰 x₁ x₂ h' ↦ ?_⟩
    rw [properSMul_iff, isProperMap_iff_ultrafilter] at h
    have ⟨(g, x), hgx1, hgx2⟩ := h.2 h'
    use g
    constructor
    · simp at hgx1
      rw [← hgx1.2, hgx1.1]
    · have := continuous_fst.tendsto (g, x)
      rw [Tendsto] at *
      calc
        map Prod.fst ↑𝒰 ≤ map Prod.fst (𝓝 (g, x)) := map_mono hgx2
        _               ≤ 𝓝 (g, x).1 := this
  · rintro ⟨cont, h⟩
    rw [properSMul_iff, isProperMap_iff_ultrafilter]
    refine ⟨by fun_prop, fun 𝒰 (x₁, x₂) hxx ↦ ?_⟩
    rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg1, hg2⟩
    use (g, x₂)
    refine ⟨by rw [hg1], ?_⟩
    rw [nhds_prod_eq, 𝒰.le_prod]
    refine ⟨hg2, ?_⟩
    change Tendsto (Prod.snd ∘ (fun gx : G × X ↦ (gx.1 • gx.2, gx.2))) ↑𝒰 (𝓝 (Prod.snd (x₁, x₂)))
    apply Filter.Tendsto.comp
    apply Continuous.tendsto
    exact continuous_snd
    assumption

/-- A group acts `G` properly on a T2 topological space `X` if and only if for all ultrafilters
`𝒰` on `X`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `𝒰.fst` converges to `g`. -/
@[to_additive "A group acts `G` properly on a T2 topological space `X` if and only if for all
ultrafilters `𝒰` on `X`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `𝒰.fst` converges to `g`."]
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 [T2Space X] : ProperSMul G X ↔
    ContinuousSMul G X ∧
    (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) 𝒰 (𝓝 (x₁, x₂)) →
    ∃ g : G, Tendsto Prod.fst (𝒰 : Filter (G × X)) (𝓝 g)) := by
  constructor
  · intro h
    have := properSMul_iff_continuousSMul_ultrafilter_tendsto.1 h
    refine ⟨this.1, fun 𝒰 x₁ x₂ h' ↦ ?_⟩
    rcases this.2 𝒰 x₁ x₂ h' with ⟨g, _, hg⟩
    exact ⟨g, hg⟩
  · rintro ⟨cont, h⟩
    rw [properSMul_iff, isProperMap_iff_ultrafilter_of_t2]
    refine ⟨by fun_prop, fun 𝒰 (x₁, x₂) hxx ↦ ?_⟩
    rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg⟩
    use (g, x₂)
    rw [nhds_prod_eq, 𝒰.le_prod]
    refine ⟨by assumption, ?_⟩
    change Tendsto (Prod.snd ∘ (fun gx : G × X ↦ (gx.1 • gx.2, gx.2))) ↑𝒰 (𝓝 (Prod.snd (x₁, x₂)))
    apply Filter.Tendsto.comp
    apply Continuous.tendsto
    exact continuous_snd
    assumption

instance [ProperSMul G X] [ContinuousSMul G X]: ProperSMul G (X × Y) where
  isProperMap_smul_pair' := sorry

instance {ι : Type*} {X : ι → Type*} [Π i, TopologicalSpace (X i)] [Π i, MulAction G (X i)]
    [∀ i, ProperSMul G (X i)] : ProperSMul G (Π i, X i) where
  isProperMap_smul_pair' := sorry

/-- If two groups `H` and `G` act on a topological space `X` such that `G` acts properly and
there exists a group homomorphims `H → G` which is a closed embedding compatible with the actions,
then `H` also acts properly on `X`. -/
@[to_additive "If two groups `H` and `G` act on a topological space `X` such that `G` acts properly
and there exists a group homomorphims `H → G` which is a closed embedding compatible with the
actions, then `H` also acts properly on `X`."]
lemma properSMul_of_closed_embedding {H : Type*} [Group H] [MulAction H X] [TopologicalSpace H]
    [ProperSMul G X] (f : H →* G) (f_clemb : ClosedEmbedding f)
    (f_compat : ∀ (h : H) (x : X), f h • x = h • x) : ProperSMul H X where
  isProperMap_smul_pair' := by
    have := IsProperMap_of_closedEmbedding f_clemb
    have : IsProperMap (Prod.map f (fun x : X ↦ x)) := IsProperMap.prod_map this isProperMap_id
    have : (fun hx : H × X ↦ (hx.1 • hx.2, hx.2)) = (fun hx ↦ (f hx.1 • hx.2, hx.2)) := by
      simp [f_compat]
    rw [this]
    change IsProperMap ((fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) ∘ (Prod.map f (fun x ↦ x)))
    apply IsProperMap.comp
    assumption
    exact isProperMap_smul_pair G X

/-- If `H` is a closed subgroup of `G` and `G` acts properly on X then so does `H`. -/
@[to_additive "If `H` is a closed subgroup of `G` and `G` acts properly on X then so does `H`."]
instance {H : Subgroup G} [ProperSMul G X] [H_closed : IsClosed (H : Set G)] : ProperSMul H X where
  isProperMap_smul_pair' := by
    have : IsProperMap (fun hx : H × X ↦ ((hx.1, hx.2) : G × X)) := by
      change IsProperMap (Prod.map ((↑) : H → G) (fun x ↦ x))
      exact IsProperMap.prod_map (isProperMap_subtype_val H_closed) isProperMap_id
    have : IsProperMap (fun hx : H × X ↦ (hx.1 • hx.2, hx.2)) := by
      change IsProperMap ((fun gx ↦ (gx.1 • gx.2, gx.2)) ∘
        (fun hx : H × X ↦ ((hx.1, hx.2) : G × X)))
      exact this.comp (isProperMap_smul_pair G X)
    assumption

lemma proj_isProperMap_of_compact [CompactSpace X] : IsProperMap (Prod.snd : X × Y → Y) := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨continuous_snd, fun 𝒰 y h ↦ ?_⟩
  have ⟨x, _, hx⟩ := isCompact_univ.ultrafilter_le_nhds (𝒰.map Prod.fst) (by rw [principal_univ]; exact le_top)
  use (x, y)
  refine ⟨rfl, ?_⟩
  calc
    ↑𝒰 ≤ (map (Prod.fst : X × Y → X) ↑𝒰) ×ˢ (map (Prod.snd : X × Y → Y) ↑𝒰) := le_prod_map_fst_snd
    _  ≤ 𝓝 x ×ˢ 𝓝 y := Filter.prod_le_prod.2 ⟨hx, h⟩
    _  = 𝓝 (x, y) := nhds_prod_eq.symm

lemma ultrafilter_le_nhds_of_compact_space [CompactSpace X] : ∀ 𝒰 : Ultrafilter X, ∃ x : X, ↑𝒰 ≤ 𝓝 x := by
  intro 𝒰
  have ⟨x, _, hx⟩ := isCompact_univ.ultrafilter_le_nhds 𝒰 (by rw [principal_univ]; exact le_top)
  exact ⟨x, hx⟩

lemma ProperSMul_of_compact_ofContinuous [TopologicalGroup G] [ContinuousSMul G X] {K : Set G} (K_comp : IsCompact K) : IsProperMap (fun gx : K × X ↦ (gx.1 : G) • gx.2) := by
  have := isCompact_iff_compactSpace.1 K_comp
  let f : Homeomorph (K × X) (K × X) :=
    {
      toFun := fun gx : K × X ↦ (gx.1, (gx.1 : G) • gx.2)
      invFun := fun gx : K × X ↦ (gx.1, (gx.1 : G)⁻¹ • gx.2)
      left_inv := by intro gx; simp
      right_inv := by intro gx; simp
    }
  exact f.isProperMap.comp proj_isProperMap_of_compact

/-- If a T2 group acts properly on a topological space, then this topological space is T2. -/
@[to_additive "If a T2 group acts properly on a topological space,
then this topological space is T2."]
theorem t2Space_of_properSMul_of_t2Group [h_proper : ProperSMul G X] [T2Space G] : T2Space X := by
  let f := fun x : X ↦ ((1 : G), x)
  have proper_f : IsProperMap f := by
    apply IsProperMap_of_closedEmbedding
    rw [closedEmbedding_iff]
    constructor
    · let g := fun gx : G × X ↦ gx.2
      have : Function.LeftInverse g f := by intro x; simp
      exact Function.LeftInverse.embedding this (by fun_prop) (by fun_prop)
    · have : range f = ({1} ×ˢ univ) := by simp
      rw [this]
      exact IsClosed.prod isClosed_singleton isClosed_univ
  rw [t2_iff_isClosed_diagonal]
  let g := fun gx : G × X ↦ (gx.1 • gx.2, gx.2)
  have proper_g : IsProperMap g := (properSMul_iff G X).1 h_proper
  have : g ∘ f = fun x ↦ (x, x) := by ext x <;> simp
  have range_gf : range (g ∘ f) = diagonal X := by simp [this]
  rw [← range_gf]
  exact (proper_f.comp proper_g).closed_range

-- Some things to generalize
#check t2Space_of_properlyDiscontinuousSMul_of_t2Space
#check Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite
