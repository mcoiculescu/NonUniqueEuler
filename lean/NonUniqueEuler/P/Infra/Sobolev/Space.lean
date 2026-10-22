import NonUniqueEuler.Defs.Infra.SobolevSpace
import NonUniqueEuler.I.Infra.Sobolev.WeakDeriv

/-!
# Proof: the bridge between `MemH`/`normH` and the Hilbert space `Hk` (library I-HK)

Proof of `I/Infra/Sobolev/Space.lean`. Manuscript-independent infrastructure (the manuscript's
`H^k` norm is `02_prelim.tex:58-66`).

* The key step is `weakPartial_ae_eq_der`: if `F.fn = f` a.e., then the chosen weak derivative
  `weakPartial γ f` agrees a.e. with the stored derivative `F.der γ` (transport the weak
  derivative with `HasWeakDerivOn.congr_ae`, then uniqueness `weakDerivOn_ae_eq`; `L²`
  functions are locally integrable).
* From it: `F` is determined by `F.fn` (`Hk.ext_fn`, via `Lp.ext` componentwise), `f ∈ H^k`
  and `‖f‖_{H^k} = ‖F‖` (`Hk.norm_eq`, `Lp.norm_def`, `eLpNorm_congr_ae`).
* Conversely, for `f ∈ H^k` the tuple `(MemLp.toLp g_γ)_γ` of chosen `L²` weak derivatives lies
  in `HkSub k` (`mem_HkSub_iff`); its `0`-th entry is `f` a.e. by `hasWeakDerivOn_nil_iff`.
* Linearity of `toHk` follows from `Hk.ext_fn` and `Lp.coeFn_add`/`Lp.coeFn_smul`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace NonUniqueEuler.Sob

/-! ### Helpers -/

private theorem locInt_of_memLp_two {g : ℂ → ℂ} (hg : MemLp g 2 (volume : Measure ℂ)) :
    LocallyIntegrableOn g univ :=
  (hg.locallyIntegrable (by norm_num)).locallyIntegrableOn univ

private theorem locInt_Lp (g : Lp ℂ 2 (volume : Measure ℂ)) :
    LocallyIntegrableOn (g : ℂ → ℂ) univ :=
  locInt_of_memLp_two (Lp.memLp g)

/-- If `F.fn = f` a.e., the chosen weak derivative `∂^γ f` is `F.der γ` a.e. -/
private theorem weakPartial_ae_eq_der {k : ℕ} {F : Hk k} {f : ℂ → ℂ}
    (h : F.fn =ᵐ[volume] f) (γ : SobIdx k) :
    weakPartial γ.1 f =ᵐ[volume] F.der γ := by
  have hw : HasWeakDerivOn univ (pdList γ.1) f (F.der γ) :=
    (F.hasWeakDeriv γ).congr_ae (by filter_upwards [h] with x hx _ using hx)
      (Filter.Eventually.of_forall fun _ _ => rfl)
  have h2 := weakDerivOn_ae_eq isOpen_univ (locInt_Lp ((F : SobTuple k).ofLp γ)) hw
  filter_upwards [h2] with x hx using hx (mem_univ x)

/-- If `F.fn = f` a.e., then `f ∈ H^k`. -/
private theorem memH_of_fn_ae {k : ℕ} {F : Hk k} {f : ℂ → ℂ} (h : F.fn =ᵐ[volume] f) :
    MemH k f := by
  rw [memH_iff]
  refine ⟨MemLp.ae_eq h (Lp.memLp ((F : SobTuple k).ofLp (idx0 k))), fun γ hγ => ?_⟩
  refine ⟨F.der ⟨γ, hγ⟩, Lp.memLp ((F : SobTuple k).ofLp ⟨γ, hγ⟩), ?_⟩
  exact (F.hasWeakDeriv ⟨γ, hγ⟩).congr_ae (by filter_upwards [h] with x hx _ using hx)
    (Filter.Eventually.of_forall fun _ _ => rfl)

/-- If `F.fn = f` a.e., then `‖f‖_{H^k} = ‖F‖`. -/
private theorem normH_of_fn_ae {k : ℕ} {F : Hk k} {f : ℂ → ℂ} (h : F.fn =ᵐ[volume] f) :
    normH k f = ‖F‖ := by
  rw [normH_eq, Hk.norm_eq, ← Finset.sum_coe_sort (multiIdx k)]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  congr 1
  rw [l2, Lp.norm_def, eLpNorm_congr_ae (weakPartial_ae_eq_der h γ)]
  rfl

private theorem fn_add_ae {k : ℕ} (F G : Hk k) : (F + G).fn =ᵐ[volume] F.fn + G.fn :=
  Lp.coeFn_add ((F : SobTuple k).ofLp (idx0 k)) ((G : SobTuple k).ofLp (idx0 k))

private theorem fn_smul_ae {k : ℕ} (c : ℂ) (F : Hk k) : (c • F).fn =ᵐ[volume] c • F.fn :=
  Lp.coeFn_smul c ((F : SobTuple k).ofLp (idx0 k))

/-! ### The interface statements -/

/-- An element of `Hk k` is determined by its function. -/
theorem Hk.ext_fn {k : ℕ} {F G : Hk k} (h : F.fn =ᵐ[volume] G.fn) : F = G := by
  apply Subtype.ext
  rw [WithLp.ext_iff]
  funext γ
  apply Lp.ext
  have h1 := weakPartial_ae_eq_der (F := F) (Filter.EventuallyEq.refl _ _) γ
  have h2 := weakPartial_ae_eq_der (F := G) h.symm γ
  exact h1.symm.trans h2

/-- The derivatives stored in `F : Hk k` are the weak derivatives of its function. -/
theorem Hk.der_ae_eq {k : ℕ} (F : Hk k) (γ : SobIdx k) :
    F.der γ =ᵐ[volume] weakPartial γ.1 F.fn :=
  (weakPartial_ae_eq_der (F := F) (Filter.EventuallyEq.refl _ _) γ).symm

/-- The function of `F : Hk k` lies in `H^k`, with `‖F.fn‖_{H^k} = ‖F‖`. -/
theorem Hk.memH_fn {k : ℕ} (F : Hk k) : MemH k F.fn ∧ normH k F.fn = ‖F‖ :=
  ⟨memH_of_fn_ae (Filter.EventuallyEq.refl _ _), normH_of_fn_ae (Filter.EventuallyEq.refl _ _)⟩

/-- `f ∈ H^k` iff `f` is (a.e.) the function of an element of `Hk k`. -/
theorem memH_iff_exists_Hk {k : ℕ} {f : ℂ → ℂ} :
    MemH k f ↔ ∃ F : Hk k, F.fn =ᵐ[volume] f := by
  constructor
  · intro hf
    rw [memH_iff] at hf
    obtain ⟨hf2, hd⟩ := hf
    choose g hg hfg using hd
    let T : SobTuple k := WithLp.toLp 2 (fun γ : SobIdx k => (hg γ.1 γ.2).toLp (g γ.1 γ.2))
    have hT : ∀ γ : SobIdx k, (T.ofLp γ : ℂ → ℂ) =ᵐ[volume] g γ.1 γ.2 := fun γ =>
      MemLp.coeFn_toLp (hg γ.1 γ.2)
    have h0 : g (0, 0) (zero_mem_multiIdx k) =ᵐ[volume] f := by
      have hnil : HasWeakDerivOn univ [] f (g (0, 0) (zero_mem_multiIdx k)) :=
        hfg (0, 0) (zero_mem_multiIdx k)
      have := (hasWeakDerivOn_nil_iff isOpen_univ (locInt_of_memLp_two hf2)
        (locInt_of_memLp_two (hg _ (zero_mem_multiIdx k)))).1 hnil
      filter_upwards [this] with x hx using (hx (mem_univ x)).symm
    have hT0 : (T.ofLp (idx0 k) : ℂ → ℂ) =ᵐ[volume] f := (hT (idx0 k)).trans h0
    have hmem : T ∈ HkSub k := by
      rw [mem_HkSub_iff]
      intro γ
      exact (hfg γ.1 γ.2).congr_ae (by filter_upwards [hT0] with x hx _ using hx.symm)
        (by filter_upwards [hT γ] with x hx _ using hx.symm)
    exact ⟨⟨T, hmem⟩, hT0⟩
  · rintro ⟨F, hF⟩
    exact memH_of_fn_ae hF

theorem toHk_fn {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) : (toHk k f).fn =ᵐ[volume] f := by
  have h := memH_iff_exists_Hk.1 hf
  unfold toHk
  rw [dite_eq_left h]
  exact h.choose_spec

theorem norm_toHk {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) : ‖toHk k f‖ = normH k f :=
  (normH_of_fn_ae (toHk_fn hf)).symm

theorem toHk_add {k : ℕ} {f g : ℂ → ℂ} (hf : MemH k f) (hg : MemH k g) :
    toHk k (f + g) = toHk k f + toHk k g := by
  have hsum : (toHk k f + toHk k g).fn =ᵐ[volume] f + g :=
    (fn_add_ae _ _).trans ((toHk_fn hf).add (toHk_fn hg))
  apply Hk.ext_fn
  exact (toHk_fn (memH_of_fn_ae hsum)).trans hsum.symm

theorem toHk_smul {k : ℕ} {f : ℂ → ℂ} (hf : MemH k f) (c : ℂ) :
    toHk k (c • f) = c • toHk k f := by
  have hsm : (c • toHk k f).fn =ᵐ[volume] c • f :=
    (fn_smul_ae _ _).trans ((toHk_fn hf).const_smul c)
  apply Hk.ext_fn
  exact (toHk_fn (memH_of_fn_ae hsm)).trans hsm.symm

theorem toHk_fn_self {k : ℕ} (F : Hk k) : toHk k F.fn = F :=
  Hk.ext_fn (toHk_fn (F.memH_fn).1)

end NonUniqueEuler.Sob
