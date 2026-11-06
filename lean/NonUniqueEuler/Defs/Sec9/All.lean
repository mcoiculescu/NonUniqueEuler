import NonUniqueEuler.Defs.Sec9.Standing
import NonUniqueEuler.Defs.Sec9.Phases
import NonUniqueEuler.Defs.Sec9.QuietRings
import NonUniqueEuler.Defs.Sec9.Handoff
import NonUniqueEuler.Defs.Sec9.KickTrue
import NonUniqueEuler.Defs.Sec9.Readout

/-!
# Relay definitions (historical `Sec9` modules)

Imports the relay data and estimates now used in Part II Sections 6–8 and
Appendix C. The `Sec9` path records the former manuscript organization;
`09_relay.tex` now contains Section 6, and the quantitative estimates are in
`C_relay_setup.tex`, `C_relay_details.tex` and `C_bootstrap_details.tex`.
The earlier `Sec5`–`Sec8` dependencies correspond to Part II Sections 2–5.

The Lean definitions retain ring-time arguments and explicit constants from the
more detailed decomposition. Current manuscript ring quantities use physical
time, with pullbacks specified in Appendix C.1 (`sec:relay-data`). The present
Proposition 6.2 (`prop:relay-step`) assembles several of these estimates and the
historical `Sec11` bootstrap lemmas; there is no identically packaged theorem
in this import module.
-/
