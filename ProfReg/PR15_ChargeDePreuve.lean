/-
  ProfReg — PR-15  renversement de la charge de la preuve
  -------------------------------------------------------
  [D-13-4 — 28/09/2026] L'ancien éponyme `charge_de_preuve_declaree` est
  renommé `sans_porteur_nomme_pas_de_renversement` : c'est un dépliage de
  `RenversementDeclare` (à une double négation près), donc une lecture,
  non le résultat de PR-15 (NT-ARCH §8ter-bis, R-3). PR-15 est porté par
  ses trois définitions et leurs témoins (fin de fichier).
  Porteur : Pierre Musseau.  7 septembre 2026.
  Lean 4 pur, sans Mathlib.

  Instrument D4 de I.3.6 §6.5 — le renversement de la charge de la preuve.
  Seul des six instruments de prescription à n'avoir aucun correspondant
  formel dans le programme (ni parmi les 31 théorèmes, ni parmi PR-1→PR-14).

  Spécification retenue, d'après I.3.6 §6.5 d :
    « Le renversement modifie la distribution des obligations de
      connaissance : il n'incombe plus aux seules entités affectées de
      prouver le dommage, mais au porteur d'une activité de démontrer sa
      compatibilité avec la protection requise. […] une obligation
      d'instruction […] qui n'est effective que si la preuve fournie est
      RECONSTRUCTIBLE, faute de quoi les acteurs affectés supportent seuls
      le coût de l'expertise. »

  Trois clauses en découlent, et une délimitation.
-/

namespace ProfRegD4

abbrev Actor := String

/-- Une preuve produite au titre d'une obligation d'instruction.
    `reconstructible` : la démonstration peut être refaite depuis le
    registre par un tiers. C'est la condition d'effectivité de I.3.6 §6.5 d. -/
structure Preuve where
  contenu         : String
  reconstructible : Bool
  deriving Repr

/-- Obligation d'instruction : qui doit démontrer la compatibilité de
    l'activité, ce qu'il a produit, et qui sont les affectés.
    `porteurCharge = none` code exactement la situation que D4 vise à
    exclure : une activité dont personne n'est tenu de démontrer la
    compatibilité. -/
structure ObligationInstruction where
  activite      : String
  porteurCharge : Option Actor
  preuve        : Option Preuve
  affectes      : List Actor

/-- La charge est satisfaite lorsqu'une preuve reconstructible a été
    produite. Produire une preuve ne suffit pas ; elle doit être refaisable. -/
def ChargeSatisfaite (o : ObligationInstruction) : Prop :=
  ∃ p, o.preuve = some p ∧ p.reconstructible = true

/-- Le renversement n'est déclaré que si un porteur de charge est nommé. -/
def RenversementDeclare (o : ObligationInstruction) : Prop :=
  o.porteurCharge ≠ none

/-- **PR-15a — pas de renversement sans porteur déclaré.**
    Une activité dont nul n'est nommé pour démontrer la compatibilité
    n'opère aucun renversement de la charge : elle laisse la charge où
    elle était, c'est-à-dire sur les affectés.

    `[LECTURE — D-13]` Dépliage de `RenversementDeclare`. Ex-
    `charge_de_preuve_declaree`, renommé le 28/09/2026 (D-13-4). -/
theorem sans_porteur_nomme_pas_de_renversement (o : ObligationInstruction)
    (h : o.porteurCharge = none) : ¬ RenversementDeclare o := by
  intro hr
  exact hr h

/-- **PR-15b — une preuve non reconstructible ne satisfait pas la charge.**
    C'est la clause d'effectivité : sans reconstructibilité, l'obligation
    d'instruction est formellement remplie et matériellement vide. -/
theorem preuve_non_reconstructible_ne_satisfait_pas
    (o : ObligationInstruction) (p : Preuve)
    (h_p : o.preuve = some p) (h_nr : p.reconstructible = false) :
    ¬ ChargeSatisfaite o := by
  intro h
  obtain ⟨q, hq, hrec⟩ := h
  have hpq : p = q := Option.some.inj (h_p.symm.trans hq)
  rw [← hpq] at hrec
  rw [h_nr] at hrec
  exact Bool.noConfusion hrec

/-- Condition de bonne formation : un acteur affecté ne peut porter la
    charge que si celle-ci a déjà été satisfaite. Autrement dit, le coût de
    l'expertise ne se déplace pas vers ceux qui subissent. -/
def BienFormeeInstruction (o : ObligationInstruction) : Prop :=
  ∀ a, a ∈ o.affectes → o.porteurCharge = some a → ChargeSatisfaite o

/-- **PR-15c — la charge ne retombe pas sur les affectés.**
    Tant que la démonstration n'est pas faite et reconstructible, aucun
    acteur affecté ne porte la charge de la preuve. C'est la clause qui
    empêche le renversement de se retourner. -/
theorem charge_ne_retombe_pas_sur_les_affectes (o : ObligationInstruction)
    (h_bf : BienFormeeInstruction o) (h_non : ¬ ChargeSatisfaite o) :
    ∀ a, a ∈ o.affectes → o.porteurCharge ≠ some a := by
  intro a ha hcontra
  exact h_non (h_bf a ha hcontra)

/-- **Une charge satisfaite et un renversement déclaré coexistent.**
    *Portée visée — déclarée, non établie par l'énoncé :* PR-15 ne juge pas la preuve.
    Le registre exige que la démonstration soit refaisable ; il ne dit rien
    de sa validité. Une preuve reconstructible et fausse satisfait PR-15.
    C'est une limite à déclarer avec le théorème, non à corriger : juger la
    preuve relèverait d'une instance, non d'un registre. -/
-- [B-10, 28/09/2026 — RENOMMÉ, ex-`PR15_ne_juge_pas_la_preuve`] Le modèle n'a pas de notion de vérité de la preuve : la « fausseté » n'est portée que par une chaîne. L'énoncé dit seulement que `ChargeSatisfaite` ne porte que sur la reconstructibilité.
theorem charge_satisfaite_et_renversement_declare_coexistent :
    ∃ o : ObligationInstruction,
      ChargeSatisfaite o ∧ RenversementDeclare o := by
  refine ⟨{ activite := "activité quelconque"
          , porteurCharge := some "exploitant"
          , preuve := some { contenu := "démonstration refaisable, non évaluée"
                           , reconstructible := true }
          , affectes := ["riverain"] }, ?_, ?_⟩
  · exact ⟨{ contenu := "démonstration refaisable, non évaluée"
           , reconstructible := true }, rfl, rfl⟩
  · simp [RenversementDeclare]

/-! ## Témoins D-13 (règle NT-ARCH §8ter-bis, R-2) — versés le 28/09/2026

`sans_porteur_nomme_pas_de_renversement`, `preuve_non_reconstructible_ne_satisfait_pas`
et `charge_ne_retombe_pas_sur_les_affectes` sont des lectures de
`RenversementDeclare`, `ChargeSatisfaite` et `BienFormeeInstruction` (R-3). Témoin
bien formé des deux premiers : `charge_satisfaite_et_renversement_declare_coexistent` ; le reste ci-dessous. -/

/-- Les trois prédicats de PR-15 discriminent. -/
theorem PR15_discrimine :
    (∃ o : ObligationInstruction, ¬ RenversementDeclare o)
    ∧ (∃ o : ObligationInstruction, ¬ ChargeSatisfaite o)
    ∧ (∃ o : ObligationInstruction, o.porteurCharge ≠ none
          ∧ BienFormeeInstruction o)
    ∧ (∃ o : ObligationInstruction, ¬ BienFormeeInstruction o) := by
  refine ⟨⟨{ activite := "x", porteurCharge := none, preuve := none, affectes := [] },
            fun h => h rfl⟩,
          ⟨{ activite := "x", porteurCharge := none, preuve := none, affectes := [] },
            (fun ⟨_, hp, _⟩ => nomatch hp)⟩,
          ⟨{ activite := "x", porteurCharge := some "a",
             preuve := some { contenu := "p", reconstructible := true }, affectes := ["a"] },
            (fun h => nomatch h),
            fun _ _ _ => ⟨_, rfl, rfl⟩⟩,
          ⟨{ activite := "x", porteurCharge := some "a", preuve := none, affectes := ["a"] },
            ?_⟩⟩
  intro h
  obtain ⟨_, hp, _⟩ := h "a" (List.mem_singleton.mpr rfl) rfl
  exact nomatch hp

end ProfRegD4
