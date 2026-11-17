/-!
# PR-32 — Le candidat de régime et l'horizon du marqueur CONV-7 (C-9)

28 septembre 2026. Décision du porteur (groupe C, C-9, option (a) avec variante) :
- **(a) homologie déclarée** : `CANDIDAT_NON_INSTANCIABLE` est, au niveau des
  régimes, le marqueur de CONV-7 — inscrit, sans effet ; la règle d'admission de
  l'arbitrage 4 (NT-ARCH §8.4) **n'est pas modifiée** ;
- **variante** : le marqueur CONV-7 reçoit un **horizon** — un critère de sortie
  ou, à défaut, une clause de caducité —, comme le régime candidat.

`[RÉSERVE DE MODÈLE]` La caducité est codée par une échéance (numéro de version) ;
à l'échéance, sans condition de réfutation déclarée, le marqueur passe à l'état
**caduc** : l'écriture reste au registre, elle ne peut plus être complétée
(modalité retenue par l'instructeur, Annexe §A.15.10, révisable).
Identités et pièces codées par `Nat`. Lean pur.

`[PISTE 3 — 28/09/2026, décision du porteur]` L'horizon est étendu à **tout marqueur E4**
(Annexe §A.15.11). Le modèle de §2 ne dépend d'aucune règle particulière :
`le_marqueur_a_toujours_un_horizon` vaut pour toute écriture marquée E4, non pour la
seule CONV-7. Aucun théorème n'est ajouté pour cette extension.
-/

namespace ProfRegPR32

/-! ## 1. C-9 — l'admission d'un régime déclaré par un collectif (arbitrage 4) -/

inductive StatutRegime where
  | admis | candidatNonInstanciable | nonInscrit
  deriving DecidableEq, Repr

structure DeclarationRegime where
  collectif      : Option Nat
  dateDelib      : Option Nat
  condRefutation : Option Nat
  /-- Critère de sortie vérifiable par un tiers (statut candidat). -/
  critereSortie  : Option Nat
  /-- Clause de caducité (statut candidat). -/
  caducite       : Option Nat
  deriving DecidableEq, Repr

def statutRegime (d : DeclarationRegime) : StatutRegime :=
  if d.collectif.isSome && d.dateDelib.isSome then
    if d.condRefutation.isSome then .admis
    else if d.critereSortie.isSome && d.caducite.isSome then .candidatNonInstanciable
    else .nonInscrit
  else .nonInscrit

/-- Seul un régime admis autorise des écritures. -/
def autoriseEcriture (d : DeclarationRegime) : Bool := statutRegime d == .admis

/-- **Sans condition de réfutation, aucun régime n'autorise d'écriture** — il est
    au mieux candidat, inscrit sans effet. -/
theorem regime_sans_refutation_n_autorise_aucune_ecriture (d : DeclarationRegime)
    (h : d.condRefutation = none) :
    statutRegime d ≠ .admis ∧ autoriseEcriture d = false := by
  unfold autoriseEcriture statutRegime
  cases (d.collectif.isSome && d.dateDelib.isSome) <;>
  cases (d.critereSortie.isSome && d.caducite.isSome) <;> simp [h]

/-- **Le candidat exige un horizon** : sans condition de réfutation, un régime
    déclaré est candidat **si et seulement si** il porte critère de sortie **et**
    caducité. -/
theorem candidat_ssi_critere_de_sortie_et_caducite (d : DeclarationRegime)
    (h₀ : d.collectif.isSome = true) (h₁ : d.dateDelib.isSome = true)
    (h : d.condRefutation = none) :
    statutRegime d = .candidatNonInstanciable ↔
      (d.critereSortie.isSome = true ∧ d.caducite.isSome = true) := by
  unfold statutRegime
  cases d.critereSortie.isSome <;> cases d.caducite.isSome <;> simp [h₀, h₁, h]

/-- **Témoin discriminant** : les trois statuts sont atteints. -/
theorem regime_temoin_discriminant :
    statutRegime ⟨some 1, some 2, some 3, none, none⟩ = .admis
  ∧ statutRegime ⟨some 1, some 2, none, some 4, some 5⟩ = .candidatNonInstanciable
  ∧ statutRegime ⟨some 1, some 2, none, some 4, none⟩ = .nonInscrit
  ∧ autoriseEcriture ⟨some 1, some 2, some 3, none, none⟩ = true := by
  decide

/-! ## 2. Variante — l'horizon du marqueur CONV-7 -/

structure EcritureMarquee where
  condRefutation : Option Nat
  /-- Critère de sortie : la pièce qui portera la condition, et son porteur. -/
  critereSortie  : Option Nat
  /-- Échéance de caducité (défaut déclaré : la version suivante du set). -/
  caducite       : Nat
  deriving DecidableEq, Repr

inductive EtatMarqueur where
  | sansMarqueur | ouvert | caduc
  deriving DecidableEq, Repr

def etatMarqueur (e : EcritureMarquee) (maintenant : Nat) : EtatMarqueur :=
  if e.condRefutation.isSome then .sansMarqueur
  else if maintenant < e.caducite then .ouvert else .caduc

/-- **Le marqueur n'est pas indéfini** : une écriture marquée atteint toujours
    un état caduc, à son échéance. -/
theorem le_marqueur_a_toujours_un_horizon (e : EcritureMarquee)
    (h : e.condRefutation = none) : ∃ t, etatMarqueur e t = .caduc :=
  ⟨e.caducite, by simp [etatMarqueur, h]⟩

/-- **Témoin discriminant** : avant l'échéance le marqueur est ouvert, après il
    est caduc ; une condition déclarée lève le marqueur. -/
theorem marqueur_temoin_discriminant :
    etatMarqueur ⟨none, some 7, 6⟩ 5 = .ouvert
  ∧ etatMarqueur ⟨none, some 7, 6⟩ 6 = .caduc
  ∧ etatMarqueur ⟨some 3, none, 6⟩ 6 = .sansMarqueur := by
  decide

end ProfRegPR32
