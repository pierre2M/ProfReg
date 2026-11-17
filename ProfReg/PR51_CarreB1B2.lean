/-
  PR-51 · `carre_B1B2_commute_sur_les_chemins_admissibles`
  =======================================================

  Appui formel de CONV-2 étendue (Annexe §A.15.9) : le carré B1↔B2.

  LE PROBLÈME
  -----------
  `V3_commutatif` (V3Verification) compare, en régime SYSTEMIQUE, le chemin
  direct et le chemin par l'inventaire, et conclut qu'ils aboutissent à la même
  phase. Il est vrai par construction (forme 1) et compare un chemin licite à un
  chemin interdit : en régime SYSTEMIQUE, la phase INVENTAIRE-ASSETS-ACTIFS est
  déclenchée et la clôture sans inventaire est interdite (PR-4,
  `cloture_interdite_sans_inventaire`). Ses deux voisins, `V3_aboutit_deliberation`
  et `V3_actoriel_inchange`, sont des lectures de fonctions à témoins croisés.
  CONV-2 ne reposait donc sur aucun résultat.

  CE QUE CE FICHIER ÉTABLIT
  -------------------------
  La règle est DÉCLARÉE comme condition de bonne formation d'un chemin — les pas
  admis entre phases (`pas`, `admissible`) — puis la commutation est CONCLUE sur
  les seuls chemins admissibles, patron de `V10a_planetaire_force_deliberation`
  (CONV-8) :
    · le chemin direct n'est pas admissible dès que la phase d'inventaire est
      requise (`le_chemin_direct_n_est_pas_admissible`) ;
    · aucun chemin admissible n'atteint la délibération sans passer par
      l'inventaire, et sans que l'écriture soit clôturable
      (`aucune_deliberation_sans_inventaire`, par induction sur le chemin) ;
    · deux chemins admissibles qui atteignent la délibération passent tous deux
      par l'inventaire, et l'écriture porte un inventaire non vide
      (`carre_B1B2_commute_sur_les_chemins_admissibles`) : la commutation tient,
      et elle n'est jamais une dispense d'inventaire ;
    · la règle discrimine (`carre_temoin_discriminant`).

  CE QUE CE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne porte pas sur le carré triangulaire NT-G7 ↔ NT-G2 ↔ NT-ARCH (2-cellule,
    horizon v6) : cette partie de CONV-2 reste procédurale.
  · Il ne démontre pas la règle des pas : elle est déclarée (CONV-2 reste une
    convention). Il établit qu'une fois la règle déclarée, la commutation
    s'ensuit sur les chemins admissibles, et qu'elle ne dispense pas d'inventaire.
  · Il ne juge pas le contenu de l'inventaire (PR-4, `PR4_ne_juge_pas_le_contenu`).

  `[RÉSERVE DE MODÈLE]` `Phase` réduit `PhaseEnquete` (V3) aux trois phases du
  carré ; V3Verification n'est pas importé, parce qu'il tire Mathlib par
  V1Verification. Les déclencheurs et la clôture sont ceux de PR-4, importés sans
  modification : la règle vaut pour les trois déclencheurs (régime SYSTEMIQUE ou
  HYBRIDE, milieu dégradé persistant, appel immanent non entendu), non pour le
  seul régime SYSTEMIQUE.

  Porteur : Pierre Musseau. Écrit le 11 octobre 2026 (option C de l'instruction
  sur CONV-2). Lean 4 pur, sans Mathlib. Importe `ProfReg.PR4_InventaireTriggerMilieu`.
-/

import ProfReg.PR4_InventaireTriggerMilieu

namespace ProfRegPR51

open ProfRegPR4

/-! ## 1. Le modèle -/

/-- Les trois phases du carré B1↔B2. -/
inductive Phase where
  | inscription | inventaire | deliberation
  deriving DecidableEq, Repr

/-- **La règle déclarée** : les pas admis entre deux phases.
    · de l'inscription à l'inventaire : toujours ;
    · de l'inventaire à la délibération : si l'écriture est clôturable (PR-4) ;
    · de l'inscription directement à la délibération : seulement si la phase
      d'inventaire n'est pas requise.
    Aucun autre pas n'est admis. -/
def pas (e : Ecriture) : Phase → Phase → Bool
  | .inscription, .inventaire   => true
  | .inventaire,  .deliberation => cloturable e
  | .inscription, .deliberation => !phaseInventaireRequise e
  | _, _                        => false

/-- Un chemin est admissible si chacun de ses pas l'est. -/
def admissible (e : Ecriture) : List Phase → Bool
  | a :: b :: r => pas e a b && admissible e (b :: r)
  | _           => true

def cheminDirect : List Phase := [.inscription, .deliberation]
def cheminParInventaire : List Phase := [.inscription, .inventaire, .deliberation]

/-! ## 2. Le chemin direct n'est pas admissible -/

/-- **PR-51 (1).** Dès que la phase d'inventaire est requise, le chemin direct
    n'est pas admissible : c'est le point que `V3_commutatif` laissait passer. -/
theorem le_chemin_direct_n_est_pas_admissible (e : Ecriture)
    (hreq : phaseInventaireRequise e = true) :
    admissible e cheminDirect = false := by
  simp [admissible, cheminDirect, pas, hreq]

/-! ## 3. Aucune délibération sans inventaire -/

/-- On n'entre en délibération, sous phase d'inventaire requise, que depuis
    l'inventaire et sur une écriture clôturable. -/
theorem entrer_en_deliberation_exige_l_inventaire (e : Ecriture) (a : Phase)
    (hreq : phaseInventaireRequise e = true) (h : pas e a .deliberation = true) :
    a = .inventaire ∧ cloturable e = true := by
  cases a with
  | inscription  => simp [pas, hreq] at h
  | inventaire   => exact ⟨rfl, h⟩
  | deliberation => simp [pas] at h

/-- **PR-51 (2) — le résultat.** Sous phase d'inventaire requise, tout chemin
    admissible qui atteint la délibération passe par l'inventaire, et l'écriture
    est clôturable. Par induction sur le chemin : la conclusion n'est pas une
    hypothèse reformulée. -/
theorem aucune_deliberation_sans_inventaire (e : Ecriture)
    (hreq : phaseInventaireRequise e = true) :
    ∀ (a : Phase) (c : List Phase), admissible e (a :: c) = true →
      Phase.deliberation ∈ c → Phase.inventaire ∈ (a :: c) ∧ cloturable e = true := by
  intro a c
  induction c generalizing a with
  | nil => intro _ h; simp at h
  | cons b r ih =>
    intro hadm hmem
    simp only [admissible, Bool.and_eq_true] at hadm
    obtain ⟨hab, hrest⟩ := hadm
    by_cases hb : b = Phase.deliberation
    · subst hb
      obtain ⟨ha, hc⟩ := entrer_en_deliberation_exige_l_inventaire e a hreq hab
      subst ha
      exact ⟨by simp, hc⟩
    · have hr : Phase.deliberation ∈ r := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hb
        · exact h
      obtain ⟨hinv, hc⟩ := ih b hrest hr
      exact ⟨List.mem_cons_of_mem _ hinv, hc⟩

/-! ## 4. Le carré commute sur les chemins admissibles -/

/-- **PR-51 (3) — CONV-2 étendue.** Sous phase d'inventaire requise, deux chemins
    admissibles partis de l'inscription qui atteignent la délibération passent
    tous deux par l'inventaire, et l'écriture porte un inventaire non vide : les
    deux chemins aboutissent à la même phase, et la commutation n'est jamais une
    dispense d'inventaire. -/
theorem carre_B1B2_commute_sur_les_chemins_admissibles (e : Ecriture)
    (hreq : phaseInventaireRequise e = true) (c₁ c₂ : List Phase)
    (h₁ : admissible e (.inscription :: c₁) = true)
    (h₂ : admissible e (.inscription :: c₂) = true)
    (d₁ : Phase.deliberation ∈ c₁) (d₂ : Phase.deliberation ∈ c₂) :
    Phase.inventaire ∈ c₁ ∧ Phase.inventaire ∈ c₂
      ∧ ∃ inv : InventaireNonVide, e.inventaire = some inv ∧ inv.val ≠ [] := by
  obtain ⟨i₁, hc⟩ := aucune_deliberation_sans_inventaire e hreq _ _ h₁ d₁
  obtain ⟨i₂, _⟩ := aucune_deliberation_sans_inventaire e hreq _ _ h₂ d₂
  refine ⟨?_, ?_, cloture_declenchee_exhibe_un_inventaire_non_vide e hreq hc⟩
  · rcases List.mem_cons.mp i₁ with h | h
    · exact absurd h (by decide)
    · exact h
  · rcases List.mem_cons.mp i₂ with h | h
    · exact absurd h (by decide)
    · exact h

/-! ## 5. Témoins (R-2, R-7) -/

def eSystemiqueInventoriee : Ecriture :=
  ⟨RegimeObl.systemique, .viable, .viable, false, some ⟨["did:mrc:inventaire"], List.cons_ne_nil _ _⟩⟩
def eSystemiqueSansInventaire : Ecriture :=
  ⟨RegimeObl.systemique, .viable, .viable, false, none⟩
def eActorielSansDeclencheur : Ecriture :=
  ⟨RegimeObl.actoriel, .viable, .viable, false, none⟩

/-- **Témoin discriminant.** Sur une écriture systémique inventoriée, le chemin
    par l'inventaire est admissible ; sans inventaire, il ne l'est pas ; le
    chemin direct ne l'est dans aucun des deux cas ; sur une écriture sans
    déclencheur, le chemin direct est admissible. La règle trie. -/
theorem carre_temoin_discriminant :
    admissible eSystemiqueInventoriee cheminParInventaire = true
  ∧ admissible eSystemiqueSansInventaire cheminParInventaire = false
  ∧ admissible eSystemiqueInventoriee cheminDirect = false
  ∧ admissible eActorielSansDeclencheur cheminDirect = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Non-vacuité du résultat.** L'hypothèse de PR-51 (2) est satisfiable : il
    existe une écriture déclenchée et un chemin admissible qui atteint la
    délibération. -/
theorem le_carre_a_un_chemin_admissible :
    phaseInventaireRequise eSystemiqueInventoriee = true
  ∧ admissible eSystemiqueInventoriee cheminParInventaire = true
  ∧ Phase.deliberation ∈ cheminParInventaire.tail :=
  ⟨rfl, rfl, by decide⟩

end ProfRegPR51
