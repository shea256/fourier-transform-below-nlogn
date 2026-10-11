import OAI.Computability.FourierTransform.NetworkLabels

namespace OAI

namespace PowerSaving.Cluster
open Matrix Binary Finset
noncomputable section

/-- Conveniently prove the shear and inverse-transpose shear together. -/
def DPath (j : J) (F : StartAxes) (s t : Lab) (M : Q) (d : ℕ) : Prop :=
  let A := basisBox j F
  ∃ N : Q, M * N = 1 ∧ Path A s t (actPoint M) d ∧ Path A s t (actPoint Nᵀ) d

lemma rat_if (P : Prop) [Decidable P] :
    (((if P then 1 else 0):ℚ):ℂ) = if P then 1 else 0 := by split <;> simp_all

lemma ap_one : actPoint (1:Q) = id := by
  funext x i
  unfold actPoint
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h
    simp [one_apply,Ne.symm h]
  · simp
lemma ap_mul (M N : Q) :
    actPoint (M*N) = actPoint M ∘ actPoint N := by
  funext x i
  simp only [actPoint, Function.comp_apply, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul,
    sum_mul,mul_sum,_root_.mul_assoc]
  rw [sum_comm]

namespace DPath
variable {j : J} {F : StartAxes} {s t u : Lab} {M N : Q} {d e : ℕ}

lemma of_id (h : Path (basisBox j F) s t id d) : DPath j F s t 1 d := by
  refine ⟨1,mul_one _,?_,?_⟩ <;> simpa [ap_one]

lemma trans (a : DPath j F s t M d) (b : DPath j F t u N e) :
    DPath j F s u (N*M) (d+e) := by
  obtain ⟨x,hx,hm,hn⟩ := a
  obtain ⟨y,hy,hl,hk⟩ := b
  refine ⟨x*y,?_,?_,?_⟩
  · rwa [Matrix.mul_assoc, ← Matrix.mul_assoc M, hx, one_mul]
  · rw [ap_mul]
    exact hm.trans hl
  · rw [transpose_mul, ap_mul]
    exact hn.trans hk

lemma paired (h : M*M=0) (g : syncBox j F s M) :
    DPath j F s s (1+M) 0 ∧ DPath j F s s (1-M) 0 := by
  have cond (i k) (h : M i k≠0) :
      frame (basisBox j F i) (s i) = frame (basisBox j F k) (s k) :=
    frame_congr _ _ _ _ (g i k h)
  constructor
  · refine ⟨1-M,inv_one_add h,Path.gate _ ?_,Path.gate _ ?_⟩
    · intro i k h
      by_cases hik : i=k
      · subst k; rfl
      · apply cond i k; simpa [one_apply,hik] using h
    · intro i k h
      by_cases hik : k=i
      · subst k; rfl
      · exact (cond k i (by simpa [one_apply,hik] using h)).symm
  · refine ⟨1+M,inv_one_sub h,Path.gate _ ?_,Path.gate _ ?_⟩
    · intro i k h
      by_cases hik : i=k
      · subst k; rfl
      · apply cond i k; simpa [one_apply,hik] using h
    · intro i k h
      by_cases hik : k=i
      · subst k; rfl
      · exact (cond k i (by simpa [one_apply,hik] using h)).symm

lemma rise (g : ∀ i, s i ⊆ t i) : DPath j F s t 1 0 :=
  of_id (Path.inc _ g)

end DPath

theorem invocation_path (j : J) (F : StartAxes) :
    DPath j F (bp j) (bend j) (1+eXY) (33*32) := by
  have h0 := DPath.paired zero_JJ (sync0 j F) |>.2
  have h1 := DPath.paired zero_RR (sync1 j F) |>.2
  have h2 := DPath.paired zero_VV (sync2 j F) |>.1
  have h3 := DPath.paired zero_GG (sync3 j F) |>.1
  have h4 := DPath.paired zero_RR (sync4 j F) |>.1
  have h5 := DPath.paired zero_JJ (sync5 j F) |>.1
  have h6 := DPath.paired zero_GG (sync6 j F) |>.2
  have h7 := DPath.paired zero_VV (sync7 j F) |>.2
  have rise : ∀ {u v : Lab}, (∀ i, u i ⊆ v i) → DPath j F u v 1 0 := fun h => DPath.rise h
  have down : DPath j F (b3 j) (b4 j) 1 (33*32) := by
    rw [← loss34 j]; exact DPath.of_id (Path.reframe ..)
  have H0 := (rise (inc_bp_b0 j)).trans h0
  have H1 := H0.trans (rise (inc_b0_b1 j)) |>.trans h1
  have H2 := H1.trans (rise (inc_b1_b2 j)) |>.trans h2
  have H3 := H2.trans (rise (inc_b2_b3 j)) |>.trans h3
  have H4 := H3.trans down |>.trans h4
  have H5 := H4.trans (rise (inc_b4_b5 j)) |>.trans h5
  have H6 := H5.trans (rise (inc_b5_b6 j)) |>.trans h6
  have H7 := H6.trans (rise (inc_b6_b7 j)) |>.trans h7
  have Hl := H7.trans (rise (inc_b7_bend j))
  rw [← net_eq, net]
  simpa only [← Matrix.mul_assoc,mul_one,one_mul,Nat.zero_add,Nat.add_zero] using Hl

/-- Induced logical actions. -/
def forward (x : Box→ℂ) : Box→ℂ
  | .inl (.inr i) => x (byy i) + x (bx i)
  | r => x r

def backward (x : Box→ℂ) : Box→ℂ
  | .inl (.inl i) => x (bx i) - x (byy i)
  | r => x r

lemma ap_add (M N : Q) (x : Box→ℂ) (r : Box) :
    actPoint (M+N) x r = actPoint M x r + actPoint N x r := by
  simp [actPoint, _root_.add_mul,sum_add_distrib]
lemma ap_sub (M N : Q) (x : Box→ℂ) (r : Box) :
    actPoint (M-N) x r = actPoint M x r - actPoint N x r := by
  simp [actPoint, _root_.sub_mul,sum_sub_distrib]

lemma ap_f : actPoint (1+eXY)=forward := by
  funext x i
  rw [ap_add, ap_one]
  rcases i with ((i|i)|(i|i)) <;>
    simp [actPoint, Fintype.sum_sum_type, eXY, one_apply, rat_if, ite_mul, forward]

lemma ap_b : actPoint (1-eXY)ᵀ=backward := by
  funext x i
  rw [transpose_sub, transpose_one, ap_sub, ap_one]
  rcases i with ((i|i)|(i|i)) <;>
    simp [actPoint, Fintype.sum_sum_type, eXY, one_apply, rat_if, ite_mul, backward]

theorem invocation (j : J) (F : StartAxes) :
    Path (basisBox j F) (bp j) (bend j) forward (33*32) ∧
    Path (basisBox j F) (bp j) (bend j) backward (33*32) := by
  obtain ⟨N, hN, H, G⟩ := invocation_path j F
  have h : N=1-eXY := by
    calc
      N = ((1-eXY)*(1+eXY))*N := by rw [inv_one_sub zero_XX, one_mul]
      _ = _ := by rw [Matrix.mul_assoc,hN,mul_one]
  subst N
  exact ⟨ap_f ▸ H,ap_b ▸ G⟩
end
end PowerSaving.Cluster

end OAI
