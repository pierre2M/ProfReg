/-
  PR-7 · `priorite_F6_F10`
  ========================

  Formalisation de **`R-PRIORITE-F6-F10`**, actée en NT-G10 §6.2 et
  ancrée sur Le Naour 2024 [VÉRIFIÉ, texte intégral consulté].

  L'ÉNONCÉ DU SET
  ---------------
  > Quand se co-activent un signal **F6** (injustice distributive et/ou
  > épistémique active) et un signal **F10** (légitimité du processus
  > délibératif), **F6 est traité en précondition** : la précondition
  > herméneutique (R-HERMENEUTIQUE, Fricker) et la protection des
  > capabilités plancher (R-CAPABILITES, Nussbaum) sont satisfaites
  > **avant** que F10 ne statue. **F10 reprend ensuite la main.**
  > **La priorité est un ordre de traitement, non un veto.**
  > *Garde-fou anti-épistocratique :* F6 ne se substitue pas au jugement
  > des concernés ; elle conditionne l'**ordre**, pas le **contenu**.

  Les trois dernières phrases ne sont pas décoratives : ce sont
  **trois gardes**, et §4 les démontre — sans quoi PR-7 se lirait comme
  un veto de F6 sur F10, c'est-à-dire exactement l'épistocratie que le
  set refuse.

  `[RÉSERVE DE MODÈLE]` `Situation` et `traiter` sont mes structures —
  réserve du §2quinquies du graphe.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib, sans import.
-/

namespace ProfRegPR7

/-! ## 1. Le modèle -/

/-- L'état d'une situation où F6 et F10 peuvent se co-activer.

    `contenu` **n'est lu par aucune transition** : c'est le jugement des
    concernés, et le garde-fou anti-épistocratique consiste exactement
    à ce qu'aucune règle d'ordre n'y touche (§4). -/
structure Situation where
  /-- Injustice distributive et/ou épistémique active. -/
  f6Actif      : Bool
  /-- Un processus délibératif est en cours (formalisme délibératif). -/
  f10Actif     : Bool
  /-- R-HERMENEUTIQUE et R-CAPABILITES satisfaites. -/
  f6Traite     : Bool
  /-- F10 a statué sur la légitimité du processus. -/
  f10Certifie  : Bool
  /-- Ce que les concernés jugent. Aucune transition ne le lit ni ne le
      modifie. -/
  contenu      : Nat
  deriving Repr

inductive Acte where
  /-- Traiter F6 : satisfaire la précondition herméneutique et les
      capabilités plancher. -/
  | traiterF6
  /-- F10 statue sur la légitimité du processus. -/
  | certifierF10
  deriving DecidableEq, Repr

/-- **La transition.** `none` = refusé.

    Une seule ligne porte la règle : F10 ne certifie pas tant qu'une
    injustice F6 active n'est pas traitée. -/
def traiter (s : Situation) : Acte → Option Situation
  | Acte.traiterF6    => some { s with f6Traite := true }
  | Acte.certifierF10 =>
      if s.f6Actif && !s.f6Traite then none
      else some { s with f10Certifie := true }

def coactivation (s : Situation) : Bool := s.f6Actif && s.f10Actif

/-! ## 2. La priorité — F10 ne certifie pas sous F6 actif non traité -/

/-- **PR-7 (1).** Sous injustice F6 active et non traitée, la
    certification de F10 est **refusée**. C'est la règle elle-même. -/
theorem F10_ne_certifie_pas_sous_F6_actif (s : Situation)
    (h6 : s.f6Actif = true) (ht : s.f6Traite = false) :
    traiter s Acte.certifierF10 = none := by
  unfold traiter
  rw [h6, ht]
  rfl

/-- **PR-7 (2).** Et le traitement de F6 est **toujours** admis : la
    précondition n'est jamais bloquée par F10. L'ordre est donc
    réalisable, pas seulement prescrit. -/
theorem traiter_F6_est_toujours_admis (s : Situation) :
    traiter s Acte.traiterF6 = some { s with f6Traite := true } := rfl

/-- **PR-7 (3) — F10 reprend la main.** Une fois F6 traité, la
    certification est admise. La priorité est **suspensive**, non
    terminale. -/
theorem F10_reprend_apres_traitement (s : Situation) (ht : s.f6Traite = true) :
    traiter s Acte.certifierF10 = some { s with f10Certifie := true } := by
  unfold traiter
  rw [ht]
  simp

/-! ## 3. L'ordre est déterminé — c'est ce que « résolue de façon
déterministe » demandait -/

/-- **PR-7 (4) — la co-activation a un ordre, et un seul.** Sur une
    situation en co-activation avec F6 non traité, la séquence
    `traiterF6` puis `certifierF10` aboutit, tandis que l'ordre inverse
    **échoue au premier pas**.

    C'est la forme exacte de « co-activation résolue de façon
    déterministe » : il ne s'agit pas de préférer un ordre, il s'agit
    qu'un seul soit praticable. -/
theorem la_coactivation_a_un_ordre_unique (s : Situation)
    (hc : coactivation s = true) (ht : s.f6Traite = false) :
    traiter s Acte.certifierF10 = none
  ∧ (∃ s', traiter s Acte.traiterF6 = some s'
           ∧ traiter s' Acte.certifierF10 = some { s' with f10Certifie := true }) := by
  have h6 : s.f6Actif = true := by
    unfold coactivation at hc
    cases hf : s.f6Actif with
    | false => rw [hf] at hc; simp at hc
    | true => rfl
  refine ⟨F10_ne_certifie_pas_sous_F6_actif s h6 ht, { s with f6Traite := true }, rfl, ?_⟩
  exact F10_reprend_apres_traitement _ rfl

/-! ## 4. Les trois gardes, et elles sont dans l'énoncé du set -/

/-- **La priorité n'est pas un veto.** Depuis toute situation, il existe
    un chemin qui aboutit à la certification de F10 : rien n'est
    définitivement bloqué. Sans cet énoncé, PR-7 se lirait comme une
    suppression de F10. -/
theorem la_priorite_n_est_pas_un_veto (s : Situation) :
    ∃ s' s'', traiter s Acte.traiterF6 = some s'
            ∧ traiter s' Acte.certifierF10 = some s''
            ∧ s''.f10Certifie = true :=
  ⟨{ s with f6Traite := true },
   { { s with f6Traite := true } with f10Certifie := true },
   rfl, F10_reprend_apres_traitement _ rfl, rfl⟩

/-- **Garde-fou anti-épistocratique — F6 conditionne l'ordre, pas le
    contenu.** Aucune transition ne modifie `contenu` : le jugement des
    concernés traverse la règle de priorité **inchangé**.

    C'est la garde la plus importante du fichier, parce que c'est celle
    dont le set redoutait l'absence. -/
theorem PR7_ne_touche_pas_au_contenu (s s' : Situation) (a : Acte)
    (h : traiter s a = some s') : s'.contenu = s.contenu := by
  cases a with
  | traiterF6 => exact (congrArg Situation.contenu (Option.some.inj h)).symm
  | certifierF10 =>
      unfold traiter at h
      cases hb : (s.f6Actif && !s.f6Traite) with
      | true => rw [hb] at h; simp at h
      | false =>
          rw [hb] at h
          simp only [Bool.false_eq_true, if_false] at h
          exact (congrArg Situation.contenu (Option.some.inj h)).symm

/-- **PR-7 ne juge pas l'injustice.** Deux situations différant par le
    seul `contenu` se comportent identiquement : la règle ne dit rien de
    ce que F6 signale, seulement de l'ordre dans lequel on le traite. -/
theorem PR7_ne_juge_pas_l_injustice (a b c d : Bool) (n₁ n₂ : Nat) (ac : Acte) :
    (traiter ⟨a, b, c, d, n₁⟩ ac).isSome = (traiter ⟨a, b, c, d, n₂⟩ ac).isSome := by
  cases ac with
  | traiterF6 => rfl
  | certifierF10 => unfold traiter; cases a <;> cases c <;> rfl

/-- **PR-7 ne vaut que sous co-activation.** Hors co-activation — F6
    inactif — la certification passe sans condition : la règle
    n'introduit aucune contrainte là où il n'y a pas de conflit. -/
theorem PR7_ne_contraint_pas_hors_coactivation (s : Situation)
    (h : s.f6Actif = false) :
    traiter s Acte.certifierF10 = some { s with f10Certifie := true } := by
  unfold traiter
  rw [h]
  simp

end ProfRegPR7
