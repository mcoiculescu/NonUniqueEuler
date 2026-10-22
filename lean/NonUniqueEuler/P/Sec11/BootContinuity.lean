import NonUniqueEuler.Defs.Sec11.Extra2Boot
import NonUniqueEuler.I.Infra.Continuity.Bootstrap
import NonUniqueEuler.I.Sec11.BootStart
import NonUniqueEuler.I.Sec11.BA
import NonUniqueEuler.H.Sec11.BootContinuity.Limit
import NonUniqueEuler.H.Sec11.BootContinuity.Extend

/-!
# Proof: Step 7 of the proof of `prop:bootstrap` (the continuity argument)

Proof of `I/Sec11/BootContinuity.lean` (`11_bootstrap.tex:540-591`): the set
`𝓑 = {t ∈ [0, T_end] : (BA°)(t)}` is all of `[0, T_end]`.

The continuity argument is `Continuity.forall_Icc_of_history` (`I/Infra/Continuity/Bootstrap.lean`)
applied to `Q(t) = (BA°)(t)` on `[0, T_end]`:
* `Q(0)`: Step 0 gives (BA*)(0), hence (BA)(0) and (BA°)(0) (`boot_start`, `BA_of_BAstar`);
* the limit step "`Q` on `[0, t)` ⇒ `Q(t)`" is `BootContinuityH.boot_limit`
  (`H/Sec11/BootContinuity/Limit.lean`, `11_bootstrap.tex:552-574`);
* the extension step "`Q` on `[0, t]`, `t < T_end` ⇒ `Q` on `(t, t + δ]`" is
  `BootContinuityH.boot_extend` (`H/Sec11/BootContinuity/Extend.lean`, `11_bootstrap.tex:576-591`).
This is the manuscript's `t_* = sup 𝓑` argument in the form of a real induction.
-/

noncomputable section

open MeasureTheory Set Metric

namespace NonUniqueEuler

namespace Relay

open RingData Datum

/-- **Step 7 of the proof of `prop:bootstrap`, the continuity argument** (`11_bootstrap.tex:540-591`):
under (N) and (P0)–(P6), (BA°)(t) holds for every `t ∈ [0, T_end]`. -/
theorem boot_continuity (S : Standing) (hS : S.Holds) (hL : S.ParamLists) :
    ∀ t ∈ Icc (0 : ℝ) S.P.Tend, S.BAcirc t := by
  apply NonUniqueEuler.Continuity.forall_Icc_of_history
  · exact (BA_of_BAstar S hS hL (boot_start S hS hL).ba_star).toBAcirc
  · intro t ht hprev
    exact BootContinuityH.boot_limit S hS hL ht hprev
  · intro t ht hprev
    exact BootContinuityH.boot_extend S hS hL ht hprev

end Relay

end NonUniqueEuler
