/-
  PR-40 · Le statut de l'écart : constaté, non vérifiable, refusé, contesté
  ========================================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur décision D-ED-13.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR35_EcritureDuale`.

  LE PROBLÈME (note du 30/09, point α)
  ------------------------------------
  PR-35 calcule l'écart en supposant les deux registres LISIBLES. Il ne
  distingue pas « B n'a pas inscrit » de « B n'a pas montré ce qu'il a
  inscrit ». Dans la source d'AX-15, la banque ADRESSE un relevé (Richard,
  Bensadon & Rambaud 2018, ch. 40 §4, p. 639) ; entre registres de
  communalité, rien ne le garantit. Confondre les cas, c'est imputer à B une
  faute que A ne peut pas constater.

  LA RÉPONSE (D-ED-13)
  --------------------
  Chaque couple de registres a un ÉTAT DE COMMUNICATION, et chaque ligne en
  écart un STATUT :
    · `extraitCommunique` — B communique les lignes qu'il porte envers A (un
      EXTRAIT, homologue du relevé ; PR-25 montre qu'il suffit à décider
      l'existence d'une contrepartie). L'écart est alors `constate`, ou
      `conteste` si B porte envers A une ligne de MÊME rôle que celle de A —
      B se déclare lui aussi créancier (ou débiteur) : il nie la ligne ;
    · `nonCommunique` — l'écart est `nonVerifiable` ;
    · `refuse` — B refuse l'écriture duale (« catégorie C », CR 2026-S09) :
      l'écart est `refuse`, et la ligne de A reste au registre (le « registre
      parallèle […] d'un point de vue unilatéral » du CR S09).

  Le statut QUALIFIE l'écart, il ne le CRÉE ni ne le COMBLE : la liste des
  lignes en écart est celle de PR-35, quel que soit l'état de communication.

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne tranche pas une contestation : c'est un statut inscrit, non une
    décision. L'arbitrage par un tiers est l'objet de D-ED-12 (ISA 505).
  · Il ne modélise ni la date ni le délai de communication.
-/

import ProfReg.PR35_EcritureDuale

namespace ProfRegPR40

open ProfRegPR35
open ProfRegPR20 (roleDeTypage)

/-! ## 1. Communication et statut -/

inductive Communication where
  | extraitCommunique
  | nonCommunique
  | refuse
  deriving DecidableEq, Repr

inductive StatutEcart where
  | constate
  | nonVerifiable
  | refuse
  | conteste
  deriving DecidableEq, Repr

variable {V : Type}

/-- B nie la ligne `l` de A : il porte envers A une ligne de **même rôle**. -/
def denegation (RA RB : Registre V) (l : Ligne V) : Bool :=
  RB.lignes.any (fun m => m.contrepartie == RA.teneur
    && decide (roleDeTypage m.typage = roleDeTypage l.typage))

/-- Le statut d'une ligne en écart. -/
def statut (com : Communication) (RA RB : Registre V) (l : Ligne V) : StatutEcart :=
  match com with
  | .extraitCommunique => if denegation RA RB l then .conteste else .constate
  | .nonCommunique     => .nonVerifiable
  | .refuse            => .refuse

/-- **L'écart qualifié** : chaque ligne de l'écart de PR-35, avec son statut. -/
def ecartQualifie (com : Communication) (RA RB : Registre V) :
    List (Ligne V × StatutEcart) :=
  (ecart RA RB).map (fun l => (l, statut com RA RB l))

/-! ## 2. Ce qui se démontre -/

/-- **Le statut ne crée ni ne comble l'écart.** Quel que soit l'état de
    communication, les lignes qualifiées sont exactement l'écart de PR-35. -/
theorem la_communication_ne_change_pas_l_ecart (com : Communication) (RA RB : Registre V) :
    (ecartQualifie com RA RB).map Prod.fst = ecart RA RB := by
  unfold ecartQualifie
  rw [List.map_map]
  exact List.map_id' _

/-- **En écriture duale, il n'y a rien à qualifier.** -/
theorem en_ecriture_duale_rien_a_qualifier (com : Communication) (RA RB : Registre V)
    (h : EcritureDuale RA RB) : ecartQualifie com RA RB = [] := by
  unfold ecartQualifie; rw [h.1]; rfl

/-! ## 3. Instance -/

def entreprise : Entite := 2
def fournisseur : Entite := 40

/-- L'entreprise inscrit une responsabilité (`D+`) envers le fournisseur. -/
def regA : Registre Nat := ⟨entreprise, [⟨fournisseur, .Dplus, 10⟩]⟩
/-- Le fournisseur n'a rien inscrit envers l'entreprise. -/
def regBVide : Registre Nat := ⟨fournisseur, []⟩
/-- Le fournisseur inscrit lui aussi un `D+` envers l'entreprise : il se
    déclare débiteur, donc nie être créancier. -/
def regBNie : Registre Nat := ⟨fournisseur, [⟨entreprise, .Dplus, 10⟩]⟩

/-- **PR-40 (1) — non vérifiable n'est pas constaté.** Mêmes registres, même
    écart ; le statut dépend de ce que A a pu lire. -/
theorem non_verifiable_n_est_pas_constate :
    ecartQualifie .nonCommunique regA regBVide = [(⟨fournisseur, .Dplus, 10⟩, .nonVerifiable)]
    ∧ ecartQualifie .extraitCommunique regA regBVide = [(⟨fournisseur, .Dplus, 10⟩, .constate)] := by
  decide

/-- **PR-40 (2) — le refus est un statut propre**, distinct de l'absence de
    communication : c'est l'entité « de catégorie C » du CR S09. -/
theorem le_refus_n_est_pas_un_silence :
    ecartQualifie .refuse regA regBVide = [(⟨fournisseur, .Dplus, 10⟩, .refuse)] := by
  decide

/-- **PR-40 (3) — la contestation.** B communique et porte une ligne de même
    rôle : l'écart est `conteste`, non `constate`. -/
theorem la_denegation_rend_l_ecart_conteste :
    ecartQualifie .extraitCommunique regA regBNie = [(⟨fournisseur, .Dplus, 10⟩, .conteste)] := by
  decide

/-- **Témoin discriminant** (R-7) de `statut` : les quatre valeurs sont
    atteintes sur la même ligne de A. -/
theorem statut_temoin_discriminant :
    statut .extraitCommunique regA regBVide ⟨fournisseur, .Dplus, 10⟩ = .constate
    ∧ statut .nonCommunique regA regBVide ⟨fournisseur, .Dplus, 10⟩ = .nonVerifiable
    ∧ statut .refuse regA regBVide ⟨fournisseur, .Dplus, 10⟩ = .refuse
    ∧ statut .extraitCommunique regA regBNie ⟨fournisseur, .Dplus, 10⟩ = .conteste := by
  decide

end ProfRegPR40
