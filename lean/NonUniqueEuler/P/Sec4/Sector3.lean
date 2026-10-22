import NonUniqueEuler.Defs.Sec4.Eigendata
import NonUniqueEuler.I.Sec4.HypN
import NonUniqueEuler.I.Sec4.EvansBasic
import NonUniqueEuler.I.Sec4.Resolvent
import NonUniqueEuler.I.Sec4.EvansSimple
import NonUniqueEuler.I.Sec4.RingFacts

/-!
# Proof: `cor:sector-3` (the sector `ℓ = 3` in reference units)

Proof of `I/Sec4/Sector3.lean` (`04_ring.tex:1205-1216`, proof `:1217-1231`). Same declaration,
statement copied verbatim.

Proof (as in the manuscript). Fix `G ∈ [0,1/50]` and `s`; `S = ringRefSetting χ` is a sector
setting (`ringRefSetting_valid`), and its Evans function is the statement layer's `evans χ 3` on
`{Re > 0}` (`ringRefSetting_evans`), hence also its `λ`-derivative there (the two functions agree
on the open half-plane, `Filter.EventuallyEq.deriv_eq`). By `hypN_lamC`, `λ = lamC χ G` is the
unique zero of `E_3(·;G)` in `{Re ≥ 9/200}`, it is simple, and `Re λ > 211/2500`. By
`spectrum_re_pos` the spectrum of `L_3(G)` on `Y^s_3` in `{Re > 0}` is the zero set of `E_3`;
hence its part in `{Re ≥ 9/200}` is `{λ}`, every other point there has `Re < 9/200`, and is an
eigenvalue on `Y^s_3` (`eigen_of_evans_eq_zero`). `evansSimple_riesz` gives `J ≠ 0`,
`ℓ_*(g_*) = 1` and the simple spectral projection `rieszSec`. The sector `-3` is the second half
of `spectrum_re_pos` (`conj` is an involution preserving `Re`).
-/

noncomputable section

open Set ComplexConjugate

namespace NonUniqueEuler

open RingData

/-- On `{Re > 0}` the Evans function of the ring in reference units and the statement layer's
`evans` have the same `λ`-derivative (`lem:evans-basic`, last assertion). -/
private lemma deriv_ringRefSetting_evans {χ : ℝ → ℝ} (hχ : IsAdmissibleCutoff χ) {z : ℂ}
    (hz : 0 < z.re) (G : ℝ) :
    deriv (fun w => (ringRefSetting χ).evans 3 w G) z = deriv (fun w => evans χ 3 w G) z := by
  apply Filter.EventuallyEq.deriv_eq
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact ringRefSetting_evans hχ 3 (by norm_num) w hw G

/-- **`cor:sector-3`** (`04_ring.tex:1205-1216`): assume (N1), (N2). For `G ∈ [0, 1/50]` and every
`s`, on `Y^s_3` of the ring in reference units: `L_3(G)` has exactly one eigenvalue
`λ_*^c(G) = Eig.lamC χ G` with `Re ≥ 9/200`; it is a simple zero of `E_3(·;G)`, `J ≠ 0`, it is
algebraically simple with the Riesz projection `g ↦ ℓ_*(g) g_*` of `thm:evans-simple`(2), and
`Re λ_*^c(G) > 211/2500`; every other point of the spectrum of `L_3(G)` in `{Re > 0}` is an
eigenvalue with real part `< 9/200`; and `L_{-3}(G)` has the complex conjugate spectrum (in
`{Re > 0}`). -/
theorem sector3 (χ : ℝ → ℝ) (hχ : IsAdmissibleCutoff χ) (h1 : N1 χ) (h2 : N2 χ) {G : ℝ}
    (hG : G ∈ Icc (0 : ℝ) (1 / 50)) (s : ℕ) :
    spectrum ℂ ((ringRefSetting χ).Lsec s 3 G) ∩ {w : ℂ | 9 / 200 ≤ w.re} = {Eig.lamC χ G} ∧
      evans χ 3 (Eig.lamC χ G) G = 0 ∧
      deriv (fun w => evans χ 3 w G) (Eig.lamC χ G) ≠ 0 ∧
      (ringRefSetting χ).J 3 (Eig.lamC χ G) G ≠ 0 ∧
      (ringRefSetting χ).ellStarY s 3 (Eig.lamC χ G) G
          ((ringRefSetting χ).gStarY s 3 (Eig.lamC χ G) G) = 1 ∧
      Dunford.IsSimpleSpectralProj ((ringRefSetting χ).Lsec s 3 G)
        ((ringRefSetting χ).rieszSec s 3 (Eig.lamC χ G) G) (Eig.lamC χ G) ∧
      211 / 2500 < (Eig.lamC χ G).re ∧
      (∀ w ∈ spectrum ℂ ((ringRefSetting χ).Lsec s 3 G), 0 < w.re → w ≠ Eig.lamC χ G →
        w.re < 9 / 200 ∧ ∃ g : Sect.Ysec s (ringRefSetting χ).Nstar 3,
          g ≠ 0 ∧ (ringRefSetting χ).Lsec s 3 G g = w • g) ∧
      spectrum ℂ ((ringRefSetting χ).Lsec s (-3) G) ∩ {w : ℂ | 0 < w.re} =
        (fun w => conj w) '' (spectrum ℂ ((ringRefSetting χ).Lsec s 3 G) ∩ {w : ℂ | 0 < w.re}) := by
  set S := ringRefSetting χ with hSdef
  have hS : S.Valid := ringRefSetting_valid hχ
  set l := Eig.lamC χ G with hldef
  obtain ⟨hre, hE0, hD, huniq⟩ := hypN_lamC χ h1 h2 hG
  have hlpos : 0 < l.re := lt_trans (by norm_num) hre
  have h3 : (1 : ℕ) ≤ 3 := by norm_num
  -- the Evans function of the setting is the statement layer's on `{Re > 0}`
  have hEv : ∀ w : ℂ, 0 < w.re → S.evans 3 w G = evans χ 3 w G := fun w hw =>
    ringRefSetting_evans hχ 3 h3 w hw G
  have hSE0 : S.evans 3 l G = 0 := by rw [hEv l hlpos]; exact hE0
  have hSD : deriv (fun w => S.evans 3 w G) l ≠ 0 := by
    rw [deriv_ringRefSetting_evans hχ hlpos G]; exact hD
  -- `lem:resolvent`, last assertion
  obtain ⟨hspec, hspecConj⟩ := SectorSetting.spectrum_re_pos S hS 3 h3 G s
  have hspec3 : ∀ w : ℂ, 0 < w.re →
      (w ∈ spectrum ℂ (S.Lsec s 3 G) ↔ evans χ 3 w G = 0) := fun w hw => by
    rw [← hEv w hw]; exact hspec w hw
  have hspecm3 : ∀ w : ℂ, 0 < w.re →
      (w ∈ spectrum ℂ (S.Lsec s (-3) G) ↔ evans χ 3 (conj w) G = 0) := fun w hw => by
    have hw' : 0 < (conj w).re := by rw [Complex.conj_re]; exact hw
    rw [← hEv (conj w) hw']; exact hspecConj w hw
  -- `thm:evans-simple`(2)
  obtain ⟨hJ, hriesz⟩ := SectorSetting.evansSimple_riesz S hS 3 h3 l hlpos G hSE0 hSD
  obtain ⟨-, hone, hproj, -⟩ := hriesz s
  refine ⟨?_, hE0, hD, hJ, hone, hproj, hre, ?_, ?_⟩
  · -- the spectrum in `{Re ≥ 9/200}` is `{λ}`
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hw, hw9⟩
      have hwpos : 0 < w.re := lt_of_lt_of_le (by norm_num) hw9
      exact huniq w hw9 ((hspec3 w hwpos).1 hw)
    · rintro rfl
      exact ⟨(hspec3 _ hlpos).2 hE0, le_of_lt (lt_trans (by norm_num) hre)⟩
  · -- the other points of the spectrum in `{Re > 0}`
    intro w hw hwpos hne
    have hEw : evans χ 3 w G = 0 := (hspec3 w hwpos).1 hw
    refine ⟨?_, ?_⟩
    · by_contra hlt
      exact hne (huniq w (not_lt.1 hlt) hEw)
    · have hSEw : S.evans 3 w G = 0 := by rw [hEv w hwpos]; exact hEw
      obtain ⟨-, -, -, -, heig⟩ := SectorSetting.eigen_of_evans_eq_zero S hS 3 h3 w hwpos G hSEw
      obtain ⟨-, hne0, hL, -⟩ := heig s
      exact ⟨S.gStarY s 3 w G, hne0, hL⟩
  · -- the sector `-3`: the conjugate spectrum
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨hw, hwpos⟩
      have hw' : 0 < (conj w).re := by rw [Complex.conj_re]; exact hwpos
      refine ⟨conj w, ⟨(hspec3 _ hw').2 ((hspecm3 w hwpos).1 hw), hw'⟩, ?_⟩
      exact Complex.conj_conj w
    · rintro ⟨u, ⟨hu, hupos⟩, rfl⟩
      have hu' : 0 < (conj u).re := by rw [Complex.conj_re]; exact hupos
      refine ⟨(hspecm3 _ hu').2 ?_, hu'⟩
      rw [Complex.conj_conj]
      exact (hspec3 u hupos).1 hu

end NonUniqueEuler
