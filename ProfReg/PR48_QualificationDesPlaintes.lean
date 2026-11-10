/-
  PR-48 · Qui qualifie une plainte de « fondée » ? (D-ED-30)
  ==========================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur décision D-ED-30.
  Note : `Note_D-ED-18_…` §10-11. Lean 4 pur, sans Mathlib.
  Importe `ProfReg.PR47_AnnotationDeDestination`.

  LE PROBLÈME
  -----------
  Directive (UE) 2024/1760, art. 14 (identique en 2024 et dans la version
  consolidée au 18/03/2026) : la société traite les plaintes, « y compris
  une procédure pour les cas où une société estime que la plainte n'est
  pas fondée » ; « lorsque la plainte est fondée, l'incidence négative …
  [est] réputée recensée » (§3) ; les plaignants sont « informés par la
  société des motifs pour lesquels une plainte a été considérée comme
  fondée ou non fondée » (§4 c). Le set : aucun teneur ne tranche l'écart
  qui le concerne (PR-41) ; seule l'instance commune arbitre (CONV-16).
  `[INCOHÉRENCE INTER-COUCHES]`.

  LA DÉCISION (D-ED-30)
  ---------------------
  1. L'avis « FONDÉE » de la société est une RECONNAISSANCE : elle inscrit
     le miroir (un teneur peut toujours reconnaître) ; l'écart se résorbe.
  2. L'avis « NON FONDÉE » est une CONTESTATION : statut `conteste`
     (PR-40). L'écart reste inscrit, NON ARBITRÉ.
  3. Le silence de la société : statut `nonVerifiable` (PR-40).
  4. Tranchent : l'INSTANCE COMMUNE (PR-43, registre de chaîne), sinon
     l'AUTORITÉ DE SUPERVISION (CS3D art. 26, voie ajoutée à PR-44).
     Une investigation par la société elle-même ne tranche pas.
  5. Une plainte RETENUE par un tiers force le miroir, comme l'avis
     « fondée » de la société `[TRANSPOSITION DÉCLARÉE — la directive
     n'attache l'effet « réputée recensée » qu'à l'avis de la société ;
     l'autorité constate un non-respect (art. 25 §4) et accorde un délai
     pour des mesures réparatrices]`.

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne dit pas sur quels critères une plainte est fondée.
  · Il ne modélise ni les délais, ni le recours contre l'autorité (§6).
  · Il ne confère aucun effet juridique à l'arbitrage de l'instance
    commune hors du contrat qui l'institue (CS3D art. 14 §6).
-/

import ProfReg.PR47_AnnotationDeDestination

namespace ProfRegPR48

open ProfRegPR35 (Entite Registre Ligne ecart completer)
open ProfRegPR40 (StatutEcart)
open ProfRegPR41 (Investigation StatutArbitre)
open ProfRegPR43 (DesignationControle arbitrerInstitue)
open ProfRegPR44 (Saisine Voie saisineRecevable)

/-! ## 1. L'avis de la société et l'issue de la plainte -/

inductive AvisSociete where
  | fondee
  | nonFondee
  | sansReponse
  deriving DecidableEq, Repr

/-- **Règles 2 et 3** : le statut de l'écart après l'avis (hors « fondée »). -/
def statutApresAvis : AvisSociete → StatutEcart
  | .fondee      => .constate    -- sans objet : l'écart est résorbé (règle 1)
  | .nonFondee   => .conteste
  | .sansReponse => .nonVerifiable

inductive IssuePlainte where
  | reconnueParSociete
  | nonArbitree (s : StatutEcart)
  | trancheeParInstance (retenue : Bool)
  | porteeDevantAutorite
  | trancheeParAutorite (retenue : Bool)
  deriving DecidableEq, Repr

/-- **L'issue de la plainte.** `soc` : la société ; `r` : le registre
    (de chaîne, ou des concernés) qui porte la plainte. -/
def issuePlainte (ds : List DesignationControle) (soc r : Entite) (a : AvisSociete)
    (inv : Option Investigation) (sais : Option Saisine) : IssuePlainte :=
  match a with
  | .fondee => .reconnueParSociete
  | _ =>
    match arbitrerInstitue ds (statutApresAvis a) inv soc r with
    | .confirmeParTiers => .trancheeParInstance true
    | .infirmeParTiers  => .trancheeParInstance false
    | _ =>
      match sais with
      | some sa =>
        if decide (sa.voie = .autoriteSupervision) && saisineRecevable sa then
          match sa.issue with
          | none   => .porteeDevantAutorite
          | some b => .trancheeParAutorite b
        else .nonArbitree (statutApresAvis a)
      | none => .nonArbitree (statutApresAvis a)

/-- La plainte est-elle retenue ? -/
def retenue : IssuePlainte → Bool
  | .reconnueParSociete      => true
  | .trancheeParInstance b   => b
  | .trancheeParAutorite b   => b
  | _                        => false

/-- **Règle 5** : le registre de la société après l'issue. -/
def miroirApres (i : IssuePlainte) (RB R : Registre Nat) : Registre Nat :=
  if retenue i then completer RB R else RB

/-! ## 2. Ce qui se démontre (général) -/

/-- **Règle 2 — « non fondée » n'est qu'une contestation** : sans tiers,
    l'écart reste inscrit, au statut `conteste`. -/
theorem non_fondee_est_une_contestation (ds : List DesignationControle) (soc r : Entite) :
    issuePlainte ds soc r .nonFondee none none = .nonArbitree .conteste := rfl

/-- **Règle 5 — plainte retenue, miroir forcé**, quel que soit qui l'a retenue. -/
theorem plainte_retenue_miroir_force (i : IssuePlainte) (RB R : Registre Nat)
    (h : retenue i = true) : ecart R (miroirApres i RB R) = [] := by
  unfold miroirApres; rw [h]
  exact ProfRegPR35.le_rapprochement_resorbe_l_ecart R RB

/-- **Rien n'est effacé** : une plainte non retenue laisse le registre de
    la société tel quel, et l'écart du registre qui porte la plainte subsiste. -/
theorem plainte_non_retenue_rien_ne_change (i : IssuePlainte) (RB R : Registre Nat)
    (h : retenue i = false) : miroirApres i RB R = RB := by
  unfold miroirApres; rw [h]; rfl

/-! ## 3. Instance : le registre de chaîne de PR-46 -/

open ProfRegPR46 (marque1 comitePilotage inspecteur dsChaine)

def plainteR : Registre Nat := ⟨comitePilotage, [⟨marque1, .Cplus, 40⟩]⟩
def regMarque : Registre Nat := ⟨marque1, []⟩

/-- **PR-48 (1) — la société ne s'arbitre pas** : sa propre « enquête »
    concluant à l'infirmation laisse la plainte contestée ; celle de
    l'inspecteur (instance commune) tranche. -/
theorem la_societe_ne_s_arbitre_pas :
    issuePlainte dsChaine marque1 comitePilotage .nonFondee
        (some ⟨marque1, false, .infirme⟩) none = .nonArbitree .conteste
    ∧ issuePlainte dsChaine marque1 comitePilotage .nonFondee
        (some ⟨inspecteur, false, .confirme⟩) none = .trancheeParInstance true := by
  decide

/-- **PR-48 (2) — sans instance, l'autorité de supervision** : saisie d'un
    rapport étayé, elle est recevable sans la société ; sa décision tranche. -/
theorem sans_instance_l_autorite :
    issuePlainte [] marque1 comitePilotage .nonFondee none
        (some ⟨.autoriteSupervision, .quelconque, false, none⟩) = .porteeDevantAutorite
    ∧ issuePlainte [] marque1 comitePilotage .nonFondee none
        (some ⟨.autoriteSupervision, .quelconque, false, some true⟩)
      = .trancheeParAutorite true
    ∧ issuePlainte [] marque1 comitePilotage .nonFondee none
        (some ⟨.negociation, .quelconque, false, some true⟩) = .nonArbitree .conteste := by
  decide

/-- **PR-48 (3) — le miroir forcé, dans les deux cas retenus.** -/
theorem le_miroir_force_sur_l_instance :
    ecart plainteR (miroirApres (.trancheeParInstance true) regMarque plainteR) = []
    ∧ ecart plainteR (miroirApres (.trancheeParInstance false) regMarque plainteR)
      = [⟨marque1, .Cplus, 40⟩] := by
  decide

/-- **Témoin discriminant** (R-7) de `issuePlainte`. -/
theorem issue_plainte_temoin_discriminant :
    issuePlainte dsChaine marque1 comitePilotage .fondee none none = .reconnueParSociete
    ∧ issuePlainte dsChaine marque1 comitePilotage .nonFondee none none = .nonArbitree .conteste
    ∧ issuePlainte dsChaine marque1 comitePilotage .sansReponse none none
      = .nonArbitree .nonVerifiable
    ∧ issuePlainte dsChaine marque1 comitePilotage .nonFondee
        (some ⟨inspecteur, false, .infirme⟩) none = .trancheeParInstance false := by
  decide

end ProfRegPR48
