/-
  PR-38 · Comptes réciproques intragroupe : même forme, finalité inverse
  =====================================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur décision D-ED-10
  (« vérifier la cohérence de AX-15 avec la réconciliation des comptes
  réciproques entre sociétés d'un même groupe »).
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR35_EcritureDuale`.

  SOURCES
  -------
  · IFRS 10, §B86(c) : « eliminate in full intragroup assets and liabilities,
    equity, income, expenses and cash flows relating to transactions between
    entities of the group » `[VÉRIFIÉ sur deux reproductions secondaires
    concordantes (BDO, IFRS in Practice 2022/2023 ; iasandifrs, 2018) — texte
    officiel IFRS non lu intégralement]`.
  · Règlement ANC n° 2020-01, art. 221-2 (version recueil 2026) : « éliminer
    les opérations et comptes entre l'entité intégrée globalement et les
    autres entités comprises dans le périmètre de consolidation »
    `[VÉRIFIÉ par extraction du PDF officiel — l'art. 251-1 n'a pas pu être
    lu, extraction tronquée]`.
  · Pratique : « s'assurer que les créances chez le vendeur sont bien égales
    aux dettes chez l'acheteur » ; écarts dus aux décalages (paiement en
    transit) ou aux erreurs de séparation des exercices, corrigés dans les
    comptes sociaux ou en consolidation — F. Pinault, FIDUCIAL Audit, mis à
    jour le 21/10/2025 `[source de pratique, non normative]`.

  CE QUE LE FICHIER ÉTABLIT
  -------------------------
  1. La réconciliation intragroupe a la FORME de AX-15 : deux teneurs, typage
     opposé, écart à rapprocher. Une paire concordante est une écriture
     duale de PR-35 (§2).
  2. Elle a une FINALITÉ INVERSE : la consolidation additionne les deux côtés
     et la paire s'annule — le lien disparaît de la vue du groupe
     (`la_consolidation_efface_ce_que_l_ecriture_duale_conserve`).
     L'écriture duale MRC, elle, conserve les deux côtés, parce que A et B
     sont distincts et que l'obligation subsiste.
  3. L'élimination SUPPOSE la concordance : une écriture duale non
     concordante laisse un solde net — l'écart de conciliation
     (`sans_concordance_l_elimination_laisse_un_ecart`).

  CE QU'IL NE FAIT PAS
  --------------------
  · Il ne modélise ni le périmètre de consolidation ni le contrôle : la
    consolidation est appliquée à deux registres donnés.
  · Il ne modélise que des paires d'une ligne ; l'extension aux listes est
    une somme, non démontrée ici.
-/

import ProfReg.PR35_EcritureDuale

namespace ProfRegPR38

open ProfRegPR35
open ProfRegPR20 (TypageIA miroirIA Role roleDeTypage)

/-! ## 1. Le solde signé d'une ligne -/

/-- Créancier : +montant ; débiteur : −montant. -/
def signe (l : Ligne Nat) : Int :=
  match roleDeTypage l.typage with
  | .creancier => (l.montant : Int)
  | .debiteur  => -(l.montant : Int)

/-- Solde signé d'un registre. -/
def solde (R : Registre Nat) : Int :=
  (R.lignes.map signe).foldr (· + ·) 0

/-- **La vue consolidée** : les deux registres additionnés, comme si les
    deux entités n'en faisaient qu'une (IFRS 10 §B86(a) : « combine like
    items »). -/
def soldeConsolide (RA RB : Registre Nat) : Int := solde RA + solde RB

/-! ## 2. Une paire concordante s'annule -/

theorem role_miroir (t : TypageIA) :
    roleDeTypage (miroirIA t) = match roleDeTypage t with
      | .creancier => .debiteur
      | .debiteur  => .creancier := by
  cases t <;> rfl

/-- **Une ligne et son miroir concordant se compensent exactement.**
    C'est ce qui rend l'élimination possible (IFRS 10 §B86(c)). -/
theorem une_paire_concordante_s_annule (a : Entite) (l m : Ligne Nat)
    (h : estMiroirConcordant a l m = true) : signe l + signe m = 0 := by
  unfold estMiroirConcordant estMiroir at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, ht⟩, hm⟩ := h
  unfold signe
  rw [ht, hm]
  cases l.typage <;> simp [roleDeTypage, miroirIA] <;> omega

/-- **PR-38, forme générale** `[D-ED-37 — 30/09/2026]` : pour toute ligne
    de montant non nul et son miroir concordant, chaque registre porte un
    solde non nul, et la vue consolidée l'annule. La consolidation efface
    TOUJOURS ce que l'écriture duale conserve (l'instance du §3 n'en est
    qu'un témoin). -/
theorem la_consolidation_efface_toujours_la_paire (a b : Entite) (l m : Ligne Nat)
    (h : estMiroirConcordant a l m = true) (hn : l.montant ≠ 0) :
    solde ⟨a, [l]⟩ ≠ 0 ∧ solde ⟨b, [m]⟩ ≠ 0 ∧ soldeConsolide ⟨a, [l]⟩ ⟨b, [m]⟩ = 0 := by
  have hs := une_paire_concordante_s_annule a l m h
  have hl : solde ⟨a, [l]⟩ = signe l := by
    show signe l + 0 = signe l
    exact Int.add_zero _
  have hm : solde ⟨b, [m]⟩ = signe m := by
    show signe m + 0 = signe m
    exact Int.add_zero _
  have hne : signe l ≠ 0 := by
    unfold signe
    cases roleDeTypage l.typage
    · show (l.montant : Int) ≠ 0
      exact Int.ofNat_ne_zero.mpr hn
    · show -(l.montant : Int) ≠ 0
      exact Int.neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr hn)
  refine ⟨by rw [hl]; exact hne, ?_, ?_⟩
  · rw [hm]; intro h0; apply hne; rw [h0, Int.add_zero] at hs; exact hs
  · show solde ⟨a, [l]⟩ + solde ⟨b, [m]⟩ = 0
    rw [hl, hm]; exact hs

/-! ## 3. Instance : deux sociétés d'un même groupe -/

def mere : Entite := 20
def filiale : Entite := 21

/-- La mère prête 100 à sa filiale ; chacune inscrit son côté. -/
def registreMere : Registre Nat := ⟨mere, [⟨filiale, .Cplus, 100⟩]⟩
def registreFiliale : Registre Nat := ⟨filiale, [⟨mere, .Dplus, 100⟩]⟩

/-- **PR-38 (1) — même forme que AX-15.** Le prêt intragroupe est une écriture
    duale concordante au sens de PR-35. -/
theorem le_pret_intragroupe_a_la_forme_de_A15 :
    EcritureDuale registreMere registreFiliale
    ∧ Concordante registreMere registreFiliale := by
  decide

/-- **PR-38 (2) — finalité inverse.** Chaque registre porte le lien (solde
    non nul de part et d'autre) ; la vue consolidée l'efface (solde nul).
    La consolidation fait disparaître ce que l'écriture duale conserve. -/
theorem la_consolidation_efface_ce_que_l_ecriture_duale_conserve :
    solde registreMere = 100 ∧ solde registreFiliale = -100
    ∧ soldeConsolide registreMere registreFiliale = 0 := by
  decide

/-- **PR-38 (3) — l'élimination suppose la concordance.** Écriture duale
    avec montants divergents (paiement en transit, erreur de séparation) :
    la paire existe des deux côtés, mais le solde consolidé n'est pas nul —
    c'est l'écart de conciliation, à rapprocher avant d'éliminer. -/
def filialeEnTransit : Registre Nat := ⟨filiale, [⟨mere, .Dplus, 97⟩]⟩

theorem sans_concordance_l_elimination_laisse_un_ecart :
    EcritureDuale registreMere filialeEnTransit
    ∧ ¬ Concordante registreMere filialeEnTransit
    ∧ soldeConsolide registreMere filialeEnTransit = 3 := by
  decide

/-- **Garde — l'écriture duale n'est pas une consolidation.** Le prêt
    bancaire de PR-35 (banque et emprunteur : deux entités sans contrôle
    commun) a la même structure et le même solde consolidé nul ; mais rien,
    dans l'écriture duale, n'autorise à additionner les deux registres. La
    somme est un calcul possible, non une vue légitime : elle n'est légitime
    que sous contrôle commun (IFRS 10, ANC 2020-01 art. 221-2), que PR-35 ne
    suppose pas. -/
theorem l_addition_est_possible_mais_non_prescrite :
    soldeConsolide registreBanque registreEmprunteur = 0
    ∧ solde registreBanque ≠ 0 ∧ solde registreEmprunteur ≠ 0 := by
  decide

end ProfRegPR38
