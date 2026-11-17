/-
  PR-47 · CONV-18 : l'annotation de destination d'un engagement de vigilance
  =========================================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur décision D-ED-27.
  Appui formel de CONV-18 (Annexe §A.15.14). Note : `Note_D-ED-18_…` §9.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR46_RegistreDeChaine`.

  LE PROBLÈME (PR-46, règles 2 et 3)
  ----------------------------------
  · La ligne duale entreprise ↔ registre de chaîne perd le SITE et l'OBJET
    (`la_projection_perd_le_fournisseur`) : la troisième arité n'est portée
    que par l'annotation.
  · La qualification de la réparation dépend du LIEN (OCDE), DÉCLARÉ par
    l'entreprise, qui a intérêt à se dire « directement liée »
    `[ENGAGEMENT SANS SYMÉTRIE]`.

  LA RÈGLE (CONV-18)
  ------------------
  1. Tout engagement porté à un registre de chaîne est ANNOTÉ : site,
     objet (parmi les objets déclarés du registre), lien déclaré. À défaut :
     mal formé, marqué `[DESTINATION NON DÉCLARÉE]`.
  2. L'INSTANCE COMMUNE (CONV-16) VÉRIFIE la destination et QUALIFIE le
     lien. Le lien RETENU par elle prime sur le lien déclaré.
  3. Tant qu'elle ne l'a pas fait, l'engagement est qualifié sur le lien
     déclaré, marqué `[LIEN NON QUALIFIÉ PAR L'INSTANCE]`.
  4. Si l'instance ne confirme pas le site, la destination est INFIRMÉE ;
     l'engagement reste inscrit (rien n'est effacé).
  5. Une vérification par un tiers non désigné ne vaut pas (PR-43).

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne dit pas COMMENT l'instance qualifie le lien (la « contribution
    substantielle » de l'OCDE, comm. 16, reste un jugement).
  · Il ne reprend pas le lien au fil du temps (« la relation … n'est
    toutefois pas figée ») : une nouvelle vérification remplace l'ancienne.
-/

import ProfReg.PR46_RegistreDeChaine

namespace ProfRegPR47

open ProfRegPR35 (Entite)
open ProfRegPR43 (DesignationControle instanceCommune)
open ProfRegPR46 (Lien Objet NatureEngagement Qualification qualifier)

/-! ## 1. Annotation, vérification -/

structure Annotation where
  site        : Option Entite
  objet       : Option Objet
  lienDeclare : Option Lien
  deriving DecidableEq, Repr

structure Verification where
  parInstance  : Entite
  siteConfirme : Bool
  lienRetenu   : Lien
  deriving DecidableEq, Repr

structure EngagementAnnote where
  entreprise   : Entite
  nature       : NatureEngagement
  montant      : Nat
  annotation   : Annotation
  verification : Option Verification
  deriving DecidableEq, Repr

/-- **Règle 1** — l'annotation est complète, et l'objet est déclaré par le registre. -/
def annotationComplete (objets : List Objet) (a : Annotation) : Bool :=
  a.site.isSome
  && (match a.objet with | some o => objets.contains o | none => false)
  && a.lienDeclare.isSome

inductive EtatCONV18 where
  | destinationNonDeclaree                    -- [DESTINATION NON DÉCLARÉE]
  | lienNonQualifie (q : Qualification)       -- [LIEN NON QUALIFIÉ PAR L'INSTANCE]
  | verifie (q : Qualification)
  | destinationInfirmee
  deriving DecidableEq, Repr

/-- **CONV-18.** `r` est le teneur du registre de chaîne. -/
def etat18 (ds : List DesignationControle) (r : Entite) (objets : List Objet)
    (e : EngagementAnnote) : EtatCONV18 :=
  if annotationComplete objets e.annotation then
    match e.annotation.lienDeclare with
    | none   => .destinationNonDeclaree
    | some l =>
      match e.verification with
      | none   => .lienNonQualifie (qualifier l e.nature)
      | some v =>
        if instanceCommune ds e.entreprise r v.parInstance then
          if v.siteConfirme then .verifie (qualifier v.lienRetenu e.nature)
          else .destinationInfirmee
        else .lienNonQualifie (qualifier l e.nature)
  else .destinationNonDeclaree

/-! ## 2. Ce qui se démontre (général) -/

/-- **Sans site, pas de destination** (règle 1). -/
theorem sans_site_destination_non_declaree (ds : List DesignationControle) (r : Entite)
    (objets : List Objet) (e : EngagementAnnote) (h : e.annotation.site = none) :
    etat18 ds r objets e = .destinationNonDeclaree := by
  simp [etat18, annotationComplete, h]

/-- **Le lien retenu par l'instance prime** (règle 2). -/
theorem le_lien_retenu_prime (ds : List DesignationControle) (r : Entite)
    (objets : List Objet) (e : EngagementAnnote) (l : Lien) (v : Verification)
    (ha : annotationComplete objets e.annotation = true)
    (hl : e.annotation.lienDeclare = some l) (hv : e.verification = some v)
    (hi : instanceCommune ds e.entreprise r v.parInstance = true)
    (hs : v.siteConfirme = true) :
    etat18 ds r objets e = .verifie (qualifier v.lienRetenu e.nature) := by
  simp [etat18, ha, hl, hv, hi, hs]

/-! ## 3. Instance : la chaîne de PR-46 -/

open ProfRegPR46 (marque1 usine comitePilotage inspecteur dsChaine objetsAccord)

def bureauPrive : Entite := 312

def annotComplete : Annotation := ⟨some usine, some .santeSecurite, some .directementLie⟩

/-- La marque 1 se déclare « directement liée » à une réparation de 40. -/
def eDeclare : EngagementAnnote := ⟨marque1, .reparation, 40, annotComplete, none⟩
/-- L'inspecteur retient « contribue ». -/
def eRequalifie : EngagementAnnote :=
  { eDeclare with verification := some ⟨inspecteur, true, .contribue⟩ }
/-- Un bureau non désigné « confirme » la déclaration : sans effet. -/
def eBureau : EngagementAnnote :=
  { eDeclare with verification := some ⟨bureauPrive, true, .directementLie⟩ }
/-- L'inspecteur ne retrouve pas l'usine. -/
def eInfirme : EngagementAnnote :=
  { eDeclare with verification := some ⟨inspecteur, false, .directementLie⟩ }
/-- Un engagement sur l'environnement, hors objets de l'Accord. -/
def eHorsObjet : EngagementAnnote :=
  ⟨marque1, .reparation, 40, ⟨some usine, some .environnement, some .cause⟩, none⟩

/-- **PR-47 (1) — la symétrie restaurée** : déclarée « directement liée »,
    la réparation n'est pas une dette (marquée) ; requalifiée « contribue »
    par l'instance, elle en devient une. -/
theorem l_instance_requalifie_le_lien :
    etat18 dsChaine comitePilotage objetsAccord eDeclare
      = .lienNonQualifie .participationVolontaire
    ∧ etat18 dsChaine comitePilotage objetsAccord eRequalifie = .verifie .dette := by
  decide

/-- **PR-47 (2) — un vérificateur non désigné ne vaut pas** (PR-43). -/
theorem un_verificateur_non_designe_ne_vaut_pas :
    etat18 dsChaine comitePilotage objetsAccord eBureau
      = .lienNonQualifie .participationVolontaire := by
  decide

/-- **PR-47 (3) — la destination infirmée, et l'objet hors registre.** -/
theorem destination_infirmee_et_objet_hors_registre :
    etat18 dsChaine comitePilotage objetsAccord eInfirme = .destinationInfirmee
    ∧ etat18 dsChaine comitePilotage objetsAccord eHorsObjet = .destinationNonDeclaree := by
  decide

/-- **Témoin discriminant** (R-7) de `etat18` : les quatre états. -/
theorem etat18_temoin_discriminant :
    etat18 dsChaine comitePilotage objetsAccord
        { eDeclare with annotation := { annotComplete with site := none } }
      = .destinationNonDeclaree
    ∧ etat18 dsChaine comitePilotage objetsAccord eDeclare
      = .lienNonQualifie .participationVolontaire
    ∧ etat18 dsChaine comitePilotage objetsAccord eRequalifie = .verifie .dette
    ∧ etat18 dsChaine comitePilotage objetsAccord eInfirme = .destinationInfirmee := by
  decide

end ProfRegPR47
