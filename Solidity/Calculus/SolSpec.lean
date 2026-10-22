import Solidity.Calculus.Derive
import Solidity.Calculus.Spec
import Solidity.Calculus.SurfaceSpec

/-!
# `sol_spec` on a scoped obligation: `⊨ᶠ cspec!{f}`

`Calculus/SurfaceSpec.lean`'s `sol_spec` (`sol_symex; sol_spec_close`) on a scoped
goal `Fml.Valid φ`, `φ` a specification's obligation (`cspec!{f}`,
`Calculus/Spec.lean`): `sol_symex` runs the scoped strategy
(`Calculus/Symex.lean`), and each leaf it leaves is closed by
`sol_spec_prep`'s steps, which read a scoped leaf without its erasure
(`Calculus/CloseScoped.lean`).  The text is today's, so `sol_spec`,
`sol_spec_close` and `sol_spec_try` work on either side.
-/
