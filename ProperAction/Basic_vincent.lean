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

variable {G X Y Z : Type*} [Group G] [MulAction G X] [MulAction G Y]
variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[to_additive]
instance [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := (isProperMap_smul_pair G X).continuous.fst

/-!
### Some typical cases of proper actions
-/

open Filter Topology

theorem foo : ProperSMul G X ↔ (∀ ℱ : Filter (G × X), ∀ x₁ x₂ : X,
    ClusterPt (x₁, x₂) (map (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) ℱ) →
    ∃ g : G, x₁ = g • x₂ ∧ ClusterPt g (map Prod.fst ℱ)) :=
  sorry

theorem foo_ultrafilter [T2Space X] : ProperSMul G X ↔ (∀ ℱ : Ultrafilter (G × X), ∀ x₁ x₂ : X,
    Tendsto (fun gx ↦ ⟨gx.1 • gx.2, gx.2⟩ : G × X → X × X) ℱ (𝓝 (x₁, x₂)) →
    ∃ g : G, Tendsto Prod.fst (ℱ : Filter (G × X)) (𝓝 g)) :=
  sorry

/-- Si f converge vers y le long du filtre F,
  et si g est continue,
  g∘ f converge vers f(y) le long de F.
-/
lemma composition {f:X→ Y}(y:Y){F: Filter X}(H1: Tendsto f F (𝓝 y))
{g:Y→ Z}(H2: Continuous g): (Tendsto (g∘ f) F (𝓝 (g y)))
:= by
  apply Filter.Tendsto.comp
  · change Tendsto g (𝓝 y) (𝓝 (g y) )
    apply Continuous.tendsto
    assumption
  · assumption


instance [hProper: ProperSMul G X] [ContinuousSMul G X] [T2Space X] [T2Space Y]: ProperSMul G (X × Y) := by
  apply foo_ultrafilter.2
  intro ℱ ⟨ x1, y1⟩  ⟨x2,y2⟩
  intro hlim
  -- change  (Tendsto (fun gz ↦ (gz.1 • gz.2, gz.2)) (↑ℱ) (𝓝 ((x1, y1), x2, y2))) at hlim
  set pXX:= fun (z: (X× Y)× (X× Y))↦ (z.1.1, z.2.1)
  have h: Continuous pXX := by
    -- ceci resoud sans reflechir : fun_prop
    apply Continuous.prod_mk
    · -- Continuous.comp
      apply Continuous.fst
      apply continuous_fst
    · -- Continuous.comp
      apply Continuous.fst
      apply continuous_snd


  -- apply Filter.tendsto_def.1 at hlim
  -- simp_rw [ Filter.tendsto_def ]
  -- Hyp: gr* F =(gn xn,gn yn,xn, yn) converge vers x1 y1 x2 y2
  -- en particulier (gn xn, xn) cv vers x1 x2
  -- propreté de l'action sur X: il existe g0 tq gn →  g0, (et xn → x2, gn xn → x1)
  -- Continuous.tendsto traduit la continuite de f en x0 en terme de filtres

  set grXY:= fun (gz:G×(X× Y))↦((gz.1•gz.2.1,gz.1• gz.2.2),(gz.2.1,gz.2.2))
  --have h2: Continuous grXY := by
  --  sorry
  have hlimXY: Tendsto grXY ℱ (𝓝 ((x1, y1), x2, y2)) := by
    exact hlim
  -- set FXYXY:= Ultrafilter.map grXY ℱ
  -- set FXX:= Ultrafilter.map (pXX∘ grXY) ℱ
  -- on veut montrer que l'ultrafiltre (FXYXY cv vers (x1,y1,x2,y2)
  -- set grX:= pXX∘ grXY
  set grX:= fun (gz:G×X)↦(gz.1•gz.2,gz.2)
  have hCgrX: Continuous grX := by
    fun_prop

  set pGX:= fun (gz:G×(X× Y))↦(gz.1, gz.2.1)
  have hpGXcont: Continuous pGX := by fun_prop

  have h3: Tendsto (grX∘ pGX) ℱ (𝓝 (x1, x2)) := by
    have hcom: grX∘ pGX = pXX∘ grXY := by
      rfl
      --ext gxy
      --· simp
      --· simp
    rw [hcom]
    apply composition ((x1,y1),x2,y2)
    · assumption
    · assumption

  -- set grX:= fun (gz:G×X)↦(gz.1•gz.2,gz.2)


  have hProper2 := isProperMap_smul_pair G X
  rw [isProperMap_iff_ultrafilter ] at hProper2
  rcases hProper2 with ⟨ hc, huf ⟩

  set FGX:= Ultrafilter.map pGX ℱ

  have hGX: Tendsto grX (FGX)  (𝓝 (x1, x2)) := by
    assumption

  apply huf at hGX
  rcases hGX  with ⟨ gx0, hGX1, hGX2⟩
  use gx0.1

  set pG:= fun (gz:G×(X× Y))↦(gz.1)
  have hpGCont: Continuous pG := by fun_prop
  set pG2:= fun (gx:G×(X))↦(gx.1)
  have hpG2Cont: Continuous pG2 := by fun_prop

  change Tendsto (pGX) ℱ (𝓝 gx0) at hGX2
--  change Tendsto (fun (gxy:G×(X×Y))↦ gxy.1) ℱ (𝓝 gx0.1)
-- change Tendsto (pG) ℱ (𝓝 gx0.1)


  have h7: (Prod.fst : G×(X× Y) → G) = pG2∘ pGX := by
    rfl

  rw [h7]
  apply composition
  · assumption
  · fun_prop


/-
  change map (fun (gxy:G×(X×Y))↦ gxy.1) ℱ ≤ (𝓝 gx0.1)
-/




--   rw [Filter.Tendsto]
--   set FG:= Ultrafilter.map (fun (gx: G×(X× Y))↦ gx.1) ℱ
-- /-
--   have heq: map (fun (gx: G×X)↦ gx.1) FGX = FG := by
--     -- unfold FG
--     -- Filter.map_compose ou Filter.map_map

--     apply Ultrafilter.map_map
--     sorry
--   -/

--   change map (fun (gxy:G×(X×Y))↦ (gxy.1,gxy.2.1)) ℱ ≤ (𝓝 gx0) at hGX2
--   apply Ultrafilter.map_map
--   sorry



  -- isProperMap_smul_pair' := by
  --   change IsProperMap (fun gz ↦ (gz.1 • gz.2, gz.2))

  --   sorry

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




variable {X' Y': Type*}[TopologicalSpace X'][TopologicalSpace Y']

-- lemme 1: pi times pi est un quotient map
lemma quotient_map_of_quotient_maps {f : X→ Y} (h_fOpen: IsOpenMap f)(h_fsurj: f.Surjective )(hf_cont: Continuous f)
{f' : X'→ Y'} (h_f2Open: IsOpenMap f')(h_f2surj: f'.Surjective )(hf2_cont: Continuous f'):
 (QuotientMap (Prod.map f f'))
:= by
  have hOpenF: IsOpenMap (Prod.map f f') := by
    exact IsOpenMap.prod h_fOpen h_f2Open
  have hFsurj: Function.Surjective (Prod.map f f') := by
    exact Function.Surjective.Prod_map h_fsurj h_f2surj
  have hFcont: Continuous (Prod.map f f') := by
    exact Continuous.prod_map hf_cont hf2_cont
  exact IsOpenMap.to_quotientMap hOpenF hFcont hFsurj


