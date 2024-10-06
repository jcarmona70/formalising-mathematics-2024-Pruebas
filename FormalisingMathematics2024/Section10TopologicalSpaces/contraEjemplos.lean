import Mathlib.Tactic

open TopologicalSpace

variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]

-- S es un subconjunto de X
variable (S : Set X)

-- `f : X → Y` es una función
variable (f : X → Y)


example (hf : Continuous f) (hS : IsCompact S) : IsCompact (f '' S) := by
  rw [isCompact_iff_finite_subcover] at *
  intros τ U hU hUS


  have ig:(f ⁻¹' (⋃ (i:τ), (U i))) = (⋃ (i:τ), (f ⁻¹' (U i)))  := by
    rw [Set.preimage_iUnion]

  have S_cont: S ⊆  (⋃ (i:τ), (f ⁻¹' (U i))) := by
    rw [← ig]
    rw [← Set.image_subset_iff]
    exact hUS

  -- Lo mismo que antes pero S_cont se sigue llamando hUS
  -- rw [Set.image_subset_iff,Set.preimage_iUnion] at hUS



  have existe:=hS (fun i => f ⁻¹' (U i)) (fun i => hf.isOpen_preimage (U i) (hU i)) S_cont
  obtain ⟨t, ht⟩ := existe
  use t
  rw [Set.image_subset_iff]
  have ig: (⋃ i ∈ t, (fun i ↦ f ⁻¹' U i) i) = (⋃ i ∈ t, f ⁻¹' U i) := by
    rfl
  rw [ig] at ht
  rw [← Set.preimage_iUnion₂] at ht

  -- have ig2: (⋃ i ∈ t, f ⁻¹' U i) = f ⁻¹' (⋃ i ∈ t, U i) := by
  --  rw [← Set.preimage_iUnion₂]
  --  rw [ig2] at ht
  -- rw [← Set.preimage_iUnion₂]
  exact ht
  done

example (hf : Continuous f) (hS : IsCompact S) : IsCompact (f '' S) := by
  rw [isCompact_iff_finite_subcover] at *
  intros τ U hU hUS


  have ig:(f ⁻¹' (⋃ (i:τ), (U i))) = (⋃ (i:τ), (f ⁻¹' (U i)))  := by
    rw [Set.preimage_iUnion]

  have S_cont: S ⊆  (⋃ (i:τ), (f ⁻¹' (U i))) := by
    rw [← ig]
    rw [← Set.image_subset_iff]
    exact hUS

  -- Lo mismo que antes pero S_cont se sigue llamando hUS
  -- rw [Set.image_subset_iff,Set.preimage_iUnion] at hUS
  -- no funciona ¿??¿?



  have existe:=hS (fun i => f ⁻¹' (U i)) (fun i => hf.isOpen_preimage (U i) (hU i)) S_cont
  obtain ⟨t, ht⟩ := existe
  use t

  simp only [Set.image_subset_iff, Set.preimage_iUnion₂]
  exact ht
  done



def Sorgenfrey : TopologicalSpace ℝ where
  IsOpen (s:Set ℝ) :=  ∀ x ∈ s, ∃ δ > 0, Set.Ico x (x + δ) ⊆ s
  isOpen_univ:= by
    intro x hx
    use 2
    constructor
    linarith
    have result:= Set.subset_univ (Set.Ico x (x + 2))
    exact result
  isOpen_inter := by
    intros s t hs ht x hx
    obtain ⟨δ, hδ, h⟩ := hs x hx.left
    obtain ⟨ε, hε, h'⟩ := ht x hx.right
    use min δ ε
    constructor
    exact lt_min hδ hε
    have subcongr: Set.Ico x (x + min δ ε) ⊆  Set.Ico x (x + ε):=by
      intro y
      intro hy
      have left :=hy.left
      have right :=hy.right
      have hmin: (min δ ε) <= ε
      exact min_le_right δ ε
      have rigth1: x + (min δ ε) <= (x + ε)
      exact add_le_add_left hmin x /-library_search-/
      constructor
      exact left
      exact lt_add_of_lt_add_left right hmin
    have subcongr': Set.Ico x (x + min δ ε) ⊆  Set.Ico x (x + δ):= by
      intro y
      intro hy
      have left :=hy.left
      have right :=hy.right
      have hmin: (min δ ε) <= δ
      exact min_le_left δ ε
      have rigth1: x + (min δ ε) <= (x + δ)
      exact add_le_add_left hmin x /-library_search-/
      constructor
      exact left
      exact lt_add_of_lt_add_left right hmin
    intro y
    intro hy
    constructor
    apply h
    apply subcongr'
    exact hy
    apply h'
    apply subcongr
    exact hy
  isOpen_sUnion := by
    intro F
    intro hF
    intro x hx
    obtain ⟨s, hs⟩ := hx
    have hs1:=hs.left
    have hx1:=hs.right
    have p:=hF s hs1 x hx1
    have s_sub:s ⊆ ⋃₀ F := by
      intro y
      intro hy
      use s
    obtain ⟨δ, hδ⟩ := p
    use δ
    constructor
    exact hδ.left
    intro y
    intro hy
    apply s_sub
    apply hδ.right
    exact hy



structure Neighborhood_system (X: Type) where
  Neighborhood_set : X → Set (Set X)
  x_in_Neighborhood : ∀ (x:X)  {N:Set X}, (N ∈ (Neighborhood_set x)) → (x ∈ N)
  Neighborhood_inter : ∀ (x:X) {N M:Set X}, (N ∈ (Neighborhood_set x)) → (M ∈ (Neighborhood_set x)) → (N ∩ M ∈ (Neighborhood_set x))
  Neighborhood_superset : ∀ (x:X) {N M:Set X},  (N ∈ (Neighborhood_set x)) → (N ⊆ M) → (M ∈ (Neighborhood_set x))
  Neigborhood_of_neighborhood : ∀ (x:X) {N: Set X}, (N ∈ (Neighborhood_set x)) → (∃ M ∈ (Neighborhood_set x), ∀ y ∈ M, (N ∈ (Neighborhood_set y)))
  total_set_is_neigborhood : ∀ (x:X), Set.univ ∈ (Neighborhood_set x)

#print Neighborhood_system.Neighborhood_set

def topology_by_Neigborhoods {X:Type} (NS: Neighborhood_system X) : TopologicalSpace X where
  IsOpen (s:Set X) := ∀ x ∈ s, ∃ N ∈ NS.Neighborhood_set x, N ⊆ s
  isOpen_univ:= by
    intro x hx
    have total := NS.total_set_is_neigborhood x
    use Set.univ


  isOpen_inter := by
    intros s t hs ht x hst
    have existss:= hs x hst.left
    obtain ⟨Ns, hNs⟩ := existss
    have existst:= ht x hst.right
    obtain ⟨Nt, hNt⟩ := existst
    have existsNst:= NS.Neighborhood_inter x hNs.left hNt.left
    use Ns ∩ Nt
    constructor
    exact existsNst
    exact Set.inter_subset_inter hNs.right hNt.right

  isOpen_sUnion := by
    intro F
    intro hF
    intro x hx
    obtain ⟨s, hs⟩ := hx
    have hs1:=hs.left
    have hx1:=hs.right
    have p:=hF s hs1 x hx1
    obtain ⟨N, hN, hN'⟩ := p
    use N
    constructor
    exact hN
    intro y
    intro hy
    use s
    constructor
    exact hs1
    apply hN'
    exact hy
