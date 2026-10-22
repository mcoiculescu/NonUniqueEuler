import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.HypN
import NonUniqueEuler.I.Sec4.EvansUnits
import NonUniqueEuler.I.Sec4.RingFacts
import NonUniqueEuler.I.Sec4.Resolvent
import NonUniqueEuler.I.Sec4.EvansSimple
import NonUniqueEuler.I.Sec4.Sector6
import NonUniqueEuler.I.Sec4.Sectors9
import NonUniqueEuler.I.Sec4.SemigroupConstruct
import NonUniqueEuler.H.Sec4.PropSU.Basic

/-!
# Helpers for `P/Sec4/PropSU`: the spectral part of `prop:SU`

The sector-by-sector proof of `(S_U)` (`04_ring.tex:1268-1288`), in ring units:

* `ℓ = 3`: by `eq:evans-units` (`evans_units`, `evans_units_deriv`), the Evans function of `Φ` is
  `E_3(·;R_c²G)`, so (N1), (N2) (`hypN_lamC`) give its unique zero `λ_*(G)` in `{Re ≥ 9/200}`,
  simple, with `Re λ_*(G) > 211/2500`; `lem:resolvent` (`spectrum_re_pos`) identifies the spectrum
  in `{Re > 0}` with the zeros, and `thm:evans-simple` (`evansSimple_riesz`) gives the Riesz
  projection.
* `ℓ = -3`: the last assertion of `lem:resolvent` and `evansSimple_riesz_conj`.
* `|ℓ| = 6`, `|ℓ| ≥ 9`: `cor:sector-6`, `cor:sectors-9` and `spectrum_re_pos_eigen`.
* `ℓ = 0`: `L_0 = 0` (`semigroupConstruct_Lsec`, `LsecFn_zero`).
-/

noncomputable section

open MeasureTheory Set ComplexConjugate

namespace NonUniqueEuler.PropSUH

open RingData Sect

/-- `G ∈ [0, Ḡ]` gives `R_c² G ∈ [0, 1/50]` (`Ḡ = R_c⁻²/50`). -/
theorem Rc_sq_mul_mem {G : ℝ} (hG : G ∈ Icc (0 : ℝ) Gbar) : Rc ^ 2 * G ∈ Icc (0 : ℝ) (1 / 50) := by
  have hRc : 0 < Rc ^ 2 := by unfold Rc; positivity
  have hRc' : Rc ≠ 0 := by unfold Rc; positivity
  constructor
  · exact mul_nonneg hRc.le hG.1
  · calc Rc ^ 2 * G ≤ Rc ^ 2 * Gbar := mul_le_mul_of_nonneg_left hG.2 hRc.le
      _ = 1 / 50 := by unfold Gbar; field_simp

/-- `L_0(G) = 0` on every `Y^s_0`. -/
theorem Lsec_zero_eq (S : SectorSetting) (hS : S.Valid) (s : ℕ) (G : ℝ) : S.Lsec s 0 G = 0 := by
  refine ContinuousLinearMap.ext fun g => ?_
  rw [zero_apply]
  apply Ysec_ext_fn
  have h := S.semigroupConstruct_Lsec hS s 0 G g
  rw [SectorSetting.LsecFn_zero] at h
  filter_upwards [h, Ysec_fn_zero (s := s) (K := S.Nstar) (ℓ := 0)] with x hx h0
  rw [hx, h0]
  simp [Ang.ofProfile]

/-- A spectrum avoiding `0`-free half planes: the spectrum of `0` meets `{Re > c}` (`c ≥ 0`) in
nothing. -/
theorem spectrum_zero_inter_re_gt {A : Type*} [Ring A] [Algebra ℂ A] {c : ℝ} (hc : 0 ≤ c) :
    spectrum ℂ (0 : A) ∩ {w : ℂ | c < w.re} = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro w ⟨hw, hre⟩
  rw [spectrum.mem_iff, sub_zero] at hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp only [Set.mem_ofPred_eq, Complex.zero_re] at hre
    linarith
  exact hw ((isUnit_iff_ne_zero.2 hw0).map _)

/-- The sectors `ℓ ∈ 3ℤ \ {0, 3, -3}` are `±6` or have `|ℓ| ≥ 9`. -/
theorem sector_cases {ℓ : ℤ} (hdvd : (3 : ℤ) ∣ ℓ) (h0 : ℓ ≠ 0) (h3 : ℓ ≠ 3) (hm3 : ℓ ≠ -3) :
    ℓ = 6 ∨ ℓ = -6 ∨ 9 ≤ |ℓ| := by
  obtain ⟨k, rfl⟩ := hdvd
  rcases le_or_gt 0 (3 * k) with h | h
  · rw [abs_of_nonneg h]
    omega
  · rw [abs_of_neg h]
    omega

/-- **The spectral part of `prop:SU`** (`04_ring.tex:1253-1259`, proof `:1268-1288`); the same
statement as `Eig.lam_SU`. -/
theorem lam_SU_core (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (hN : NumericalHypothesis χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) Gbar) (s : ℕ) :
    211 / 2500 < (Eig.lam χ G).re ∧
      spectrum ℂ (Lin.Lsec χ s 3 G) ∩ {w : ℂ | 9 / 200 < w.re} = {Eig.lam χ G} ∧
      (ringPhiSetting χ).ellStarY s 3 (Eig.lam χ G) G
          ((ringPhiSetting χ).gStarY s 3 (Eig.lam χ G) G) = 1 ∧
      Dunford.IsSimpleSpectralProj (Lin.Lsec χ s 3 G)
        ((ringPhiSetting χ).rieszSec s 3 (Eig.lam χ G) G) (Eig.lam χ G) ∧
      spectrum ℂ (Lin.Lsec χ s (-3) G) ∩ {w : ℂ | 9 / 200 < w.re} = {conj (Eig.lam χ G)} ∧
      (ringPhiSetting χ).ellStarBarY s 3 (Eig.lam χ G) G
          ((ringPhiSetting χ).gStarBarY s 3 (Eig.lam χ G) G) = 1 ∧
      Dunford.IsSimpleSpectralProj (Lin.Lsec χ s (-3) G)
        ((ringPhiSetting χ).rieszSecBar s 3 (Eig.lam χ G) G) (conj (Eig.lam χ G)) ∧
      ∀ ℓ : ℤ, (3 : ℤ) ∣ ℓ → ℓ ≠ 3 → ℓ ≠ -3 →
        spectrum ℂ (Lin.Lsec χ s ℓ G) ∩ {w : ℂ | 9 / 200 < w.re} = ∅ := by
  set S := ringPhiSetting χ with hSdef
  have hS : S.Valid := ringPhiSetting_valid hχ
  have hGc := Rc_sq_mul_mem hG
  obtain ⟨h211, hE, hE', huniq⟩ := hypN_lamC χ hN.n1 hN.n2 hGc
  have hlam : Eig.lam χ G = Eig.lamC χ (Rc ^ 2 * G) := rfl
  rw [← hlam] at h211 hE hE' huniq
  have hz : 0 < (Eig.lam χ G).re := by linarith
  have hEΦ : S.evans 3 (Eig.lam χ G) G = 0 := by
    rw [hSdef, evans_units hχ 3 (by norm_num) _ hz G]
    exact hE
  have hEΦ' : deriv (fun w => S.evans 3 w G) (Eig.lam χ G) ≠ 0 := by
    rw [hSdef, evans_units_deriv hχ 3 (by norm_num) _ hz G]
    exact hE'
  obtain ⟨_, hR⟩ := S.evansSimple_riesz hS 3 (by norm_num) _ hz G hEΦ hEΦ'
  have hRc := S.evansSimple_riesz_conj hS 3 (by norm_num) _ hz G hEΦ hEΦ' s
  obtain ⟨hsp3, hspm3⟩ := S.spectrum_re_pos hS 3 (by norm_num) G s
  refine ⟨h211, ?_, (hR s).2.1, (hR s).2.2.1, ?_, hRc.2.2.2.2.1, hRc.2.2.2.2.2.1, ?_⟩
  · -- the sector `3`
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hw, hre⟩
      have hw' : w ∈ spectrum ℂ (S.Lsec s ((3 : ℕ) : ℤ) G) := hw
      have h0 := (hsp3 w (by linarith)).1 hw'
      rw [hSdef, evans_units hχ 3 (by norm_num) w (by linarith) G] at h0
      exact huniq w hre.le h0
    · rintro rfl
      exact ⟨(hsp3 _ hz).2 hEΦ, by linarith⟩
  · -- the sector `-3`
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hw, hre⟩
      have hw' : w ∈ spectrum ℂ (S.Lsec s (-((3 : ℕ) : ℤ)) G) := hw
      have h0 := (hspm3 w (by linarith)).1 hw'
      have hre' : 9 / 200 ≤ (conj w).re := by rw [Complex.conj_re]; exact hre.le
      rw [hSdef, evans_units hχ 3 (by norm_num) (conj w) (by rw [Complex.conj_re]; linarith) G]
        at h0
      have h1 := huniq (conj w) hre' h0
      rw [← h1, Complex.conj_conj]
    · rintro rfl
      refine ⟨?_, by rw [Complex.conj_re]; linarith⟩
      have h1 := (hspm3 (conj (Eig.lam χ G)) (by rw [Complex.conj_re]; exact hz)).2
        (by rw [Complex.conj_conj]; exact hEΦ)
      exact h1
  · -- the other sectors
    intro ℓ hdvd h3 hm3
    by_cases h0 : ℓ = 0
    · subst h0
      have hL0 : Lin.Lsec χ s 0 G = 0 := Lsec_zero_eq S hS s G
      rw [hL0]
      exact spectrum_zero_inter_re_gt (by norm_num)
    · apply Set.eq_empty_of_forall_notMem
      rintro w ⟨hw, hre⟩
      have hre' : 9 / 200 < w.re := hre
      have hw' : w ∈ spectrum ℂ (S.Lsec s ℓ G) := hw
      obtain ⟨g, hg, hgz⟩ := S.spectrum_re_pos_eigen hS ℓ h0 G s w (by linarith) hw'
      rcases sector_cases hdvd h0 h3 hm3 with h | h | h
      · have := sector_six hχ hN.n3 S (Or.inr rfl) G ℓ (Or.inl h) g w hg hgz (by linarith)
        linarith
      · have := sector_six hχ hN.n3 S (Or.inr rfl) G ℓ (Or.inr h) g w hg hgz (by linarith)
        linarith
      · have := sectors_ge9 hχ hN.n3 S (Or.inr rfl) G ℓ h g w hg hgz (by linarith)
        linarith

end NonUniqueEuler.PropSUH
