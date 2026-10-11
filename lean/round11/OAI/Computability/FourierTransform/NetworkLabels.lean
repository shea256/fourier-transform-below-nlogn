import OAI.Computability.FourierTransform.ScalarNetwork

namespace OAI
namespace PowerSaving.Cluster
open Matrix Binary Finset

-- Throughout one invocation a product basis for each physical wire.
abbrev BoxBasis := Box → OBase Blocks
abbrev StartAxes := J → OBase H

def basisBox (j : J) (F : StartAxes) : BoxBasis
  | .inl (.inl i) | .inl (.inr i) => OBase.tensor (Function.update F j (tripBase i))
  | .inr (.inl s) => OBase.tensor (Function.update F j (pairBase s.1 s.2))
  | .inr (.inr _) => OBase.tensor (Function.update F j (OBase.canonical H))

abbrev Lab := Box → Mask
def stamp (x y s c d : Mask) : Lab
  | .inl (.inl _) => x
  | .inl (.inr _) => y
  | .inr (.inl p) => if neighbor p.1 p.2 then s else d
  | .inr (.inr _) => c

lemma stamp_mono {x₁ y₁ s₁ c₁ d₁ x₂ y₂ s₂ c₂ d₂ : Mask}
    (hx : x₁ ⊆ x₂) (hy : y₁ ⊆ y₂) (hs : s₁ ⊆ s₂)
    (hc : c₁ ⊆ c₂) (hd : d₁ ⊆ d₂) :
    ∀ r, stamp x₁ y₁ s₁ c₁ d₁ r ⊆ stamp x₂ y₂ s₂ c₂ d₂ r := by
  rintro ((x|y)|(s|c))
  · exact hx
  · exact hy
  · by_cases h : neighbor s.1 s.2
    · simpa only [stamp, ite_eq_left h] using hs
    · simpa only [stamp, ite_eq_right h] using hd
  · exact hc

def bp (j : J) := stamp (xstart j 0) (ystart j 0) ∅ ∅ ∅
def b0 (j : J) := stamp (xstart j 0) (ystart j 0) (ystart j 1) ∅ ∅
def b1 (j : J) := stamp (xstart j 0) (belt j) (ystart j 1) (belt j) ∅
def b2 (j : J) := stamp (xstep j 0) (belt j) (xstep j 0) (belt j) ∅
def b3 (j : J) := stamp (big j) (belt j) (xstep j 0) (big j) ∅
def b4 (j : J) := stamp (big j) (belt j) (xstep j 0) (belt j) ∅
def b5 (j : J) := stamp (big j) (ystep j 0) (ystep j 1) (belt j) ∅
def b6 (j : J) := stamp (big j) (ystep j 0) (ystep j 1) (big j) ∅
def b7 (j : J) := stamp (big j) (ystep j 0) (big j) (big j) ∅
def bend (j : J) := stamp (big j) (ystep j 0) univ univ univ

lemma inc_bp_b0 (j : J) : ∀ r, bp j r ⊆ b0 j r := by
  apply stamp_mono <;> first | exact fun _ h => h | simp


lemma inc_b0_b1 (j : J) : ∀ r, b0 j r ⊆ b1 j r := by
  apply stamp_mono <;> first | exact fun _ h => h | (try simp (config := { failIfUnchanged := false }))
  · intro k hk
    rw [in_belt]
    rw [in_ystart] at hk
    tauto

lemma inc_b1_b2 (j : J) : ∀ r, b1 j r ⊆ b2 j r := by
  apply stamp_mono <;> first | exact fun _ h => h | (try simp (config := { failIfUnchanged := false }))
  · intro k hk
    rw [in_xstep]
    rw [in_xstart] at hk
    tauto
  · intro k hk
    rw [in_xstep]
    rw [in_ystart] at hk
    tauto

lemma inc_b2_b3 (j : J) : ∀ r, b2 j r ⊆ b3 j r := by
  apply stamp_mono <;> first | exact fun _ h => h | (try simp (config := { failIfUnchanged := false }))
  · intro k hk
    rw [in_big]
    rw [in_xstep] at hk
    tauto
  · intro k hk
    rw [in_big]
    rw [in_belt] at hk
    tauto

lemma loss34 (j : J) :
    loss (b3 j) (b4 j)=33*32 := by
  -- exactly centers
  unfold loss
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [b3,b4,stamp,belt_drop]

lemma inc_b4_b5 (j : J) : ∀ r, b4 j r ⊆ b5 j r := by
  apply stamp_mono <;> first | exact fun _ h => h | (try simp (config := { failIfUnchanged := false }))
  · intro k hk
    rw [in_ystep]
    rw [in_belt] at hk
    tauto
  · intro k hk
    rw [in_ystep]
    rw [in_xstep] at hk
    -- if slot=0 then slot≠1
    obtain ⟨hf,h|h⟩ := hk
    · tauto
    · exact ⟨hf, Or.inr (by rw [h]; exact piv)⟩

lemma inc_b5_b6 (j : J) : ∀ r, b5 j r ⊆ b6 j r := by
  apply stamp_mono <;> first | exact fun _ h => h | (try simp (config := { failIfUnchanged := false }))
  · intro k hk
    rw [in_big]
    rw [in_belt] at hk
    tauto

lemma inc_b6_b7 (j : J) : ∀ r, b6 j r ⊆ b7 j r := by
  apply stamp_mono <;> first | exact fun _ h => h | (try simp (config := { failIfUnchanged := false }))
  · intro k hk
    rw [in_big]
    rw [in_ystep] at hk
    tauto

lemma inc_b7_bend (j : J) : ∀ r, b7 j r ⊆ bend j r := by
  apply stamp_mono <;> first | exact fun _ h => h | simp


/-- A support condition checks the Gate/projection interaction. -/
def syncBox (j : J) (F : StartAxes) (L : Lab) (Q : Matrix Box Box ℚ) :=
  ∀ i k, Q i k ≠ 0 →
    ((basisBox j F i).mat (L i)) = ((basisBox j F k).mat (L k))

lemma upd_same (j : J) (F : StartAxes) (u v : OBase H) :
    ∀ k, k ≠ j → Function.update F j u k = Function.update F j v k := by
  intro k h; simp [Function.update_of_ne h]

lemma sync_J (j : J) (F : StartAxes) (L : Lab)
    (h : ∀ a : Side, neighbor a.1 a.2 →
      (basisBox j F (byy a.2)).mat (L (byy a.2)) =
      (basisBox j F (bs a)).mat (L (bs a))) :
    syncBox j F L eJ := by
  rintro ((x|y)|(s|c)) ((x'|y')|(s'|c')) hh <;>
    simp only [eJ, giveAux, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
               Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
               Matrix.zero_apply, ne_eq, not_true] at hh
  unfold jlocal at hh
  split at hh
  next he =>
    have eq := he.2
    subst y
    exact h s' he.1
  next he => contradiction

lemma sync_R (j : J) (F : StartAxes) {x s c d}
    (hc : c=belt j) : syncBox j F (stamp x (belt j) s c d) eR := by
  subst c
  rintro ((x|y)|(s|c)) ((x'|y')|(s'|c')) hh <;>
    simp only [eR, giveAux, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
               Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
               Matrix.zero_apply, ne_eq, not_true] at hh
  apply belt_proj
  exact upd_same j F _ _  -- match?

lemma sync_V (j : J) (F : StartAxes) (L : Lab)
    (h : ∀ a : Side, neighbor a.1 a.2 →
      (basisBox j F (bs a)).mat (L (bs a)) =
      (basisBox j F (bx a.1)).mat (L (bx a.1))) :
    syncBox j F L eV := by
  rintro ((x|y)|(s|c)) ((x'|y')|(s'|c')) hh <;>
    simp only [eV,takeAux, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
               Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
               Matrix.zero_apply, ne_eq, not_true] at hh
  unfold vlocal at hh
  split at hh
  next he =>
    have eq := he.2
    subst x'
    exact h s he.1
  next he => contradiction

lemma sync_G (j : J) (F : StartAxes) {s y c d}
    (hc : c=big j) : syncBox j F (stamp (big j) y s c d) eG := by
  subst c
  rintro ((x|y)|(s|c)) ((x'|y')|(s'|c')) hh <;>
    simp only [eG,takeAux, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
               Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
               Matrix.zero_apply, ne_eq, not_true] at hh
  apply big_proj; exact upd_same j F _ _

lemma sync0 (j : J) (F : StartAxes) : syncBox j F (b0 j) eJ := by
  apply sync_J
  intro p h
  simp only [b0,  stamp, ite_eq_left h, basisBox]
  apply ystart_proj (upd_same j F _ _)
  simp [h]
lemma sync1 (j : J) (F : StartAxes) : syncBox j F (b1 j) eR :=
  sync_R j F rfl
lemma sync2 (j : J) (F : StartAxes) : syncBox j F (b2 j) eV := by
  apply sync_V
  intro p h
  simp only [b2, stamp,ite_eq_left h,basisBox]
  apply xstep_proj (upd_same j F _ _)
  simp [h]
lemma sync3 (j : J) (F : StartAxes) : syncBox j F (b3 j) eG :=
  sync_G j F rfl
lemma sync4 (j : J) (F : StartAxes) : syncBox j F (b4 j) eR :=
  sync_R j F rfl
lemma sync5 (j : J) (F : StartAxes) : syncBox j F (b5 j) eJ := by
  apply sync_J
  intro p h
  simp only [b5, stamp,ite_eq_left h,basisBox]
  apply ystep_proj (upd_same j F _ _)
  simp [h]
lemma sync6 (j : J) (F : StartAxes) : syncBox j F (b6 j) eG :=
  sync_G j F rfl
lemma sync7 (j : J) (F : StartAxes) : syncBox j F (b7 j) eV := by
  apply sync_V
  intro p h
  simp only [b7, stamp,ite_eq_left h,basisBox]
  exact big_proj (upd_same j F _ _)

end PowerSaving.Cluster

end OAI
