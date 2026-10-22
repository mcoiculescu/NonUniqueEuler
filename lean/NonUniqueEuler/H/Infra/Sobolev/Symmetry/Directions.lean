import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import NonUniqueEuler.Defs.Infra.Sobolev
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv
import NonUniqueEuler.H.Infra.Sobolev.Symmetry.ChainRule

/-!
# Helper: weak derivatives of `H^k` functions in arbitrary directions

For `f ∈ H^k` and directions `w₁, …, wₙ ∈ ℂ` (`n ≤ k`), the weak derivative
`∂_{w₁} ⋯ ∂_{wₙ} f` exists in `L²`, and
`‖∂_{w₁} ⋯ ∂_{wₙ} f‖²_{L²} ≤ ∏ |wᵢ|² · 2ⁿ · ∑_{|β| = n} ‖∂^β f‖²_{L²}`
(`dirs`, the Hilbert–Schmidt type bound used for rotations; one Cauchy–Schwarz inequality per
direction, writing `w = (Re w) · 1 + (Im w) · i`). The counting lemma `sum_levels_le` regroups
the multi-indices by order.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob.SymmAux

/-! ### `L²` bookkeeping -/

theorem locInt_of_memLp {f : ℂ → ℂ} (hf : MemLp f 2 volume) : LocallyIntegrableOn f univ :=
  (hf.locallyIntegrable (by norm_num)).locallyIntegrableOn univ

theorem l2_congr_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) : l2 f = l2 g := by
  unfold l2
  rw [eLpNorm_congr_ae h]

theorem l2_add_le {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    l2 (f + g) ≤ l2 f + l2 g := by
  unfold l2
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hf.1 hg.1 (by norm_num))

theorem l2_const_mul (c : ℂ) (f : ℂ → ℂ) : l2 (fun x => c * f x) = ‖c‖ * l2 f := by
  unfold l2
  have : (fun x => c * f x) = c • f := rfl
  rw [this, eLpNorm_const_smul, ENNReal.toReal_mul]
  simp

/-- The chosen weak derivative agrees a.e. with any `L²` weak derivative on the plane. -/
theorem weakDerivOn_univ_ae_eq {vs : List ℂ} {f g : ℂ → ℂ} (hg : MemLp g 2 volume)
    (h : HasWeakDerivOn univ vs f g) : weakDerivOn univ vs f =ᵐ[volume] g := by
  have := weakDerivOn_ae_eq (V := univ) isOpen_univ (locInt_of_memLp hg) h
  filter_upwards [this] with x hx using hx (mem_univ x)

/-- If an `L²` weak derivative exists, the chosen one is an `L²` weak derivative with the same
norm. -/
theorem weakDerivOn_univ_spec {vs : List ℂ} {f g : ℂ → ℂ} (hg : MemLp g 2 volume)
    (h : HasWeakDerivOn univ vs f g) :
    MemLp (weakDerivOn univ vs f) 2 volume ∧ HasWeakDerivOn univ vs f (weakDerivOn univ vs f) ∧
      l2 (weakDerivOn univ vs f) = l2 g := by
  have hae := weakDerivOn_univ_ae_eq hg h
  exact ⟨hg.ae_eq hae.symm, (weakDerivOn_spec (locInt_of_memLp hg) h).2, l2_congr_ae hae⟩

/-- For `f ∈ H^k` and `|γ| ≤ k`, the chosen weak derivative is an `L²` weak derivative. -/
theorem memH_spec {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    MemLp (weakPartial γ f) 2 volume ∧ HasWeakDerivOn univ (pdList γ) f (weakPartial γ f) := by
  obtain ⟨g, hg, h⟩ := (memH_iff.1 hf).2 γ hγ
  obtain ⟨s1, s2, -⟩ := weakDerivOn_univ_spec hg h
  exact ⟨s1, s2⟩

/-- The chosen weak partial derivative agrees a.e. with any `L²` weak derivative. -/
theorem weakPartial_ae_eq_of {γ : ℕ × ℕ} {f g : ℂ → ℂ} (hg : MemLp g 2 volume)
    (h : HasWeakDerivOn univ (pdList γ) f g) : weakPartial γ f =ᵐ[volume] g :=
  weakDerivOn_univ_ae_eq hg h

/-! ### Lists of coordinate directions -/

/-- A list of coordinate directions `1`, `i`. -/
def IsCoordList (us : List ℂ) : Prop := ∀ u ∈ us, u = 1 ∨ u = Complex.I

theorem exists_perm_pdList :
    ∀ us : List ℂ, IsCoordList us →
      ∃ β : ℕ × ℕ, β.1 + β.2 = us.length ∧ us.Perm (pdList β)
  | [], _ => ⟨(0, 0), rfl, by simp [pdList]⟩
  | u :: us, h => by
    obtain ⟨β, hβ, hp⟩ := exists_perm_pdList us (fun v hv => h v (List.mem_cons_of_mem _ hv))
    rcases h u (List.mem_cons_self) with rfl | rfl
    · refine ⟨(β.1 + 1, β.2), by simp; omega, ?_⟩
      simp only [pdList, List.replicate_succ, List.cons_append]
      exact hp.cons 1
    · refine ⟨(β.1, β.2 + 1), by simp; omega, ?_⟩
      simp only [pdList, List.replicate_succ]
      exact (hp.cons Complex.I).trans List.perm_middle.symm

theorem IsCoordList.append_one {ps : List ℂ} (h : IsCoordList ps) : IsCoordList (ps ++ [1]) := by
  intro u hu
  rcases List.mem_append.1 hu with hu | hu
  · exact h u hu
  · left; simpa using hu

theorem IsCoordList.append_I {ps : List ℂ} (h : IsCoordList ps) :
    IsCoordList (ps ++ [Complex.I]) := by
  intro u hu
  rcases List.mem_append.1 hu with hu | hu
  · exact h u hu
  · right; simpa using hu

/-! ### The directional bound -/

/-- The sum `∑_{|β| = n, |β| ≤ k} ‖∂^β f‖²_{L²}` of one order. -/
theorem level_nonneg (k n : ℕ) (f : ℂ → ℂ) :
    0 ≤ ∑ β ∈ (multiIdx k).filter (fun β => β.1 + β.2 = n), l2 (weakPartial β f) ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sq_add_le_mul (a b x y : ℝ) :
    (|a| * x + |b| * y) ^ 2 ≤ (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
  have ha : |a| ^ 2 = a ^ 2 := sq_abs a
  have hb : |b| ^ 2 = b ^ 2 := sq_abs b
  nlinarith [sq_nonneg (|a| * y - |b| * x)]

/-- Base case: coordinate directions. -/
theorem dirs_base {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) {ps : List ℂ} (hps : IsCoordList ps)
    (hlen : ps.length ≤ k) :
    MemLp (weakDerivOn univ ps f) 2 volume ∧
      HasWeakDerivOn univ ps f (weakDerivOn univ ps f) ∧
      l2 (weakDerivOn univ ps f) ^ 2 ≤
        ∑ β ∈ (multiIdx k).filter (fun β => β.1 + β.2 = ps.length), l2 (weakPartial β f) ^ 2 := by
  obtain ⟨β, hβ, hp⟩ := exists_perm_pdList ps hps
  have hβk : β ∈ multiIdx k := mem_multiIdx.2 (hβ.trans_le hlen)
  obtain ⟨h1, h2⟩ := memH_spec hf hβk
  obtain ⟨s1, s2, s3⟩ := weakDerivOn_univ_spec h1 (h2.perm hp.symm)
  refine ⟨s1, s2, ?_⟩
  rw [s3]
  exact Finset.single_le_sum (f := fun β => l2 (weakPartial β f) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_filter.2 ⟨hβk, hβ⟩)

/-- Weak derivatives of `f ∈ H^k` in arbitrary directions `ws` (after coordinate directions
`ps`), with the Hilbert–Schmidt type bound. -/
theorem dirs {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) :
    ∀ (ws ps : List ℂ), IsCoordList ps → ps.length + ws.length ≤ k →
      MemLp (weakDerivOn univ (ps ++ ws) f) 2 volume ∧
      HasWeakDerivOn univ (ps ++ ws) f (weakDerivOn univ (ps ++ ws) f) ∧
      l2 (weakDerivOn univ (ps ++ ws) f) ^ 2 ≤
        (ws.map fun w => ‖w‖ ^ 2).prod * 2 ^ ws.length *
          ∑ β ∈ (multiIdx k).filter (fun β => β.1 + β.2 = ps.length + ws.length),
            l2 (weakPartial β f) ^ 2
  | [], ps, hps, hlen => by
    simp only [List.append_nil, List.map_nil, List.prod_nil, List.length_nil, pow_zero,
      mul_one, one_mul, add_zero] at hlen ⊢
    exact dirs_base hf hps hlen
  | w :: ws, ps, hps, hlen => by
    have hlen' : (ps ++ [1]).length + ws.length ≤ k := by simp at hlen ⊢; omega
    have hlenI : (ps ++ [Complex.I]).length + ws.length ≤ k := by simp at hlen ⊢; omega
    obtain ⟨a1, a2, a3⟩ := dirs hf ws (ps ++ [1]) hps.append_one hlen'
    obtain ⟨b1, b2, b3⟩ := dirs hf ws (ps ++ [Complex.I]) hps.append_I hlenI
    have hn1 : (ps ++ [1]).length + ws.length = ps.length + (w :: ws).length := by simp; omega
    have hnI : (ps ++ [Complex.I]).length + ws.length = ps.length + (w :: ws).length := by
      simp; omega
    rw [hn1] at a3
    rw [hnI] at b3
    set g₁ := weakDerivOn univ (ps ++ [1] ++ ws) f
    set g₂ := weakDerivOn univ (ps ++ [Complex.I] ++ ws) f
    set T := ∑ β ∈ (multiIdx k).filter (fun β => β.1 + β.2 = ps.length + (w :: ws).length),
      l2 (weakPartial β f) ^ 2
    set P := (ws.map fun w => ‖w‖ ^ 2).prod
    -- move the new direction to the front
    have e1 : (ps ++ [1] ++ ws).Perm (1 :: (ps ++ ws)) := by
      rw [List.append_assoc, List.singleton_append]; exact List.perm_middle
    have eI : (ps ++ [Complex.I] ++ ws).Perm (Complex.I :: (ps ++ ws)) := by
      rw [List.append_assoc, List.singleton_append]; exact List.perm_middle
    have hf2 : MemLp f 2 volume := (memH_iff.1 hf).1
    have hc := hasWeakDerivOn_cons_add (locInt_of_memLp hf2) (locInt_of_memLp a1)
      (locInt_of_memLp b1) w.re w.im (a2.perm e1) (b2.perm eI)
    have hw : w.re • (1 : ℂ) + w.im • Complex.I = w := by
      apply Complex.ext <;> simp
    rw [hw] at hc
    have hc' := hc.perm (List.perm_middle (l₁ := ps) (a := w) (l₂ := ws)).symm
    have hG : MemLp (fun x => (w.re : ℂ) * g₁ x + (w.im : ℂ) * g₂ x) 2 volume :=
      (a1.const_mul _).add (b1.const_mul _)
    obtain ⟨s1, s2, s3⟩ := weakDerivOn_univ_spec hG hc'
    refine ⟨s1, s2, ?_⟩
    rw [s3]
    have hle : l2 (fun x => (w.re : ℂ) * g₁ x + (w.im : ℂ) * g₂ x) ≤
        |w.re| * l2 g₁ + |w.im| * l2 g₂ := by
      have := l2_add_le (a1.const_mul (w.re : ℂ)) (b1.const_mul (w.im : ℂ))
      rw [l2_const_mul, l2_const_mul] at this
      simp only [Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    have hP : 0 ≤ P := List.prod_nonneg fun x hx => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx; positivity
    have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hnorm : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    calc l2 (fun x => (w.re : ℂ) * g₁ x + (w.im : ℂ) * g₂ x) ^ 2
        ≤ (|w.re| * l2 g₁ + |w.im| * l2 g₂) ^ 2 :=
          pow_le_pow_left₀ (l2_nonneg _) hle 2
      _ ≤ (w.re ^ 2 + w.im ^ 2) * (l2 g₁ ^ 2 + l2 g₂ ^ 2) :=
          sq_add_le_mul _ _ _ _
      _ ≤ ‖w‖ ^ 2 * (P * 2 ^ ws.length * T + P * 2 ^ ws.length * T) := by
          rw [hnorm]
          exact mul_le_mul_of_nonneg_left (add_le_add a3 b3) (sq_nonneg _)
      _ = ((w :: ws).map fun w => ‖w‖ ^ 2).prod * 2 ^ (w :: ws).length * T := by
          show _ = (‖w‖ ^ 2 * P) * 2 ^ (ws.length + 1) * T
          ring

/-! ### Regrouping multi-indices by order -/

theorem card_level_le (k n : ℕ) :
    ((multiIdx k).filter (fun γ => n = γ.1 + γ.2)).card ≤ k + 1 := by
  have h := Finset.card_le_card_of_injOn (s := (multiIdx k).filter (fun γ => n = γ.1 + γ.2))
    (t := Finset.range (k + 1)) (fun γ => γ.1) ?_ ?_
  · simpa using h
  · intro γ hγ
    have := (Finset.mem_filter.1 hγ).1
    rw [mem_multiIdx] at this
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro γ hγ γ' hγ' he
    have h1 := (Finset.mem_filter.1 hγ).2
    have h2 := (Finset.mem_filter.1 hγ').2
    simp only at he
    ext <;> omega

/-- `∑_{|γ| ≤ k} 2^{|γ|} ∑_{|β| = |γ|} X_β ≤ 4^k ∑_{|β| ≤ k} X_β` for `X ≥ 0`. -/
theorem sum_levels_le (k : ℕ) (X : ℕ × ℕ → ℝ) (hX : ∀ β, 0 ≤ X β) :
    ∑ γ ∈ multiIdx k, (2 : ℝ) ^ (γ.1 + γ.2) *
        ∑ β ∈ (multiIdx k).filter (fun β => β.1 + β.2 = γ.1 + γ.2), X β ≤
      4 ^ k * ∑ β ∈ multiIdx k, X β := by
  have hlev : ∀ γ : ℕ × ℕ, 0 ≤ ∑ β ∈ (multiIdx k).filter (fun β => β.1 + β.2 = γ.1 + γ.2), X β :=
    fun γ => Finset.sum_nonneg fun _ _ => hX _
  calc ∑ γ ∈ multiIdx k, (2 : ℝ) ^ (γ.1 + γ.2) *
        ∑ β ∈ (multiIdx k).filter (fun β => β.1 + β.2 = γ.1 + γ.2), X β
      ≤ ∑ γ ∈ multiIdx k, (2 : ℝ) ^ k *
        ∑ β ∈ (multiIdx k).filter (fun β => β.1 + β.2 = γ.1 + γ.2), X β := by
        refine Finset.sum_le_sum fun γ hγ => mul_le_mul_of_nonneg_right ?_ (hlev γ)
        exact pow_le_pow_right₀ (by norm_num) (mem_multiIdx.1 hγ)
    _ = (2 : ℝ) ^ k * ∑ β ∈ multiIdx k,
        ((multiIdx k).filter (fun γ => β.1 + β.2 = γ.1 + γ.2)).card * X β := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ k * ∑ β ∈ multiIdx k, ((k : ℝ) + 1) * X β := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun β _ => ?_) (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (hX β)
        exact_mod_cast card_level_le k (β.1 + β.2)
    _ ≤ 4 ^ k * ∑ β ∈ multiIdx k, X β := by
        rw [← Finset.mul_sum, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => hX _)
        have h1 : ((k : ℝ) + 1) ≤ 2 ^ k := by
          exact_mod_cast Nat.lt_two_pow_self
        calc (2 : ℝ) ^ k * ((k : ℝ) + 1) ≤ 2 ^ k * 2 ^ k :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 4 ^ k := by rw [← mul_pow]; norm_num

end NonUniqueEuler.Sob.SymmAux
