import Lean.Meta.Tactic.TryThis
import Batteries.Tactic.Lemma

set_option lang.lemmaCmd true

open Lean Elab Command Meta Tactic

set_option hygiene false in
elab tk:"help_me!" : command => liftTermElabM do
  let decl := (← getEnv).find? `TPwL.re_add
  if decl.isSome then
    logInfo "What should `lemma im_add` be?\nYou may need 10 lemmas analogous to `re_add`!"
  else
    let stx ← `(command| @[simp] lemma re_add {a b : Ri} : (a + b).re = a.re + b.re := sorry )
    TryThis.addSuggestion tk stx

elab tk:"hint_inverse" : tactic => do
  TryThis.addSuggestion tk (← `(tactic| rintro ⟨d⟩ ))
