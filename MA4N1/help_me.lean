import Lean.Meta.Tactic.TryThis
import Batteries.Tactic.Lemma

set_option lang.lemmaCmd true

open Lean Elab Command Meta Tactic

set_option hygiene false in
elab tk:"help_me!" : command => liftTermElabM do
  if (← getEnv).contains `TPwL.re_add then
    logInfo "What should `lemma im_add` be?\nYou may need 10 lemmas analogous to `re_add`!"
  else
    let stx ← `(command| @[simp] lemma re_add {a b : Ri} : (a + b).re = a.re + b.re := sorry )
    TryThis.addSuggestion tk stx

elab tk:"hint_inverse" : tactic => do
  TryThis.addSuggestion tk (← `(tactic| rintro ⟨d⟩ ))

elab "help_all" : command => liftTermElabM do
  TryThis.addSuggestion (← getRef) "@[simp] lemma re_zero : (0 : Ri).re = 0 := rfl
@[simp] lemma im_zero : (0 : Ri).im = 0 := rfl
@[simp] lemma re_one  : (1 : Ri).re = 1 := rfl
@[simp] lemma im_one  : (1 : Ri).im = 0 := rfl

@[simp] lemma re_add {a b : Ri} : (a + b).re = a.re + b.re := rfl
@[simp] lemma im_add {a b : Ri} : (a + b).im = a.im + b.im := rfl
@[simp] lemma re_mul {a b : Ri} : (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] lemma im_mul {a b : Ri} : (a * b).im = a.re * b.im + a.im * b.re := rfl

@[simp] lemma re_inv {a : Ri} : (a⁻¹).re =   a.re / (a.re ^ 2 + a.im ^ 2) := rfl
@[simp] lemma im_inv {a : Ri} : (a⁻¹).im = - a.im / (a.re ^ 2 + a.im ^ 2) := rfl"
