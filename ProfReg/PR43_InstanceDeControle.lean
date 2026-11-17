/-
  PR-43 · L'instance de contrôle : le tiers institué d'une écriture duale
  ======================================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur décision D-ED-20
  (« instituer le tiers d'un registre de communalité »). Appui formel de
  CONV-16 (Annexe §A.15.12).
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR41_ArbitrageParUnTiers`,
  `ProfReg.PR37_RegistreDuMilieu` et `ProfReg.PR39_RealisationDuMaintien`.

  LE PROBLÈME
  -----------
  PR-41 et AX-16 fondent la PLACE du tiers — aucun teneur ne tranche l'écart
  qui le concerne ; un tiers lié non plus — jamais son IDENTITÉ. N'importe
  quel tiers non lié pouvait arbitrer.

  CE QUE LE SET AVAIT DÉJÀ
  ------------------------
  · NT-G6 §2.1, d'après Rochfeld, Cornu & Martin 2021 : la communalité se
    qualifie « selon les instances (attributaire, délibérative, de contrôle) »
    — l'instance de contrôle porte « un pouvoir de contrôle du respect de ces
    décisions ».
  · Note APC du 20/09/2026 (registre de communalité, rubriques) :
    « Communauté de contrôle | Qui est habilité à faire respecter les droits
    inscrits ».
  · CR 2025-S25 (porteur, 20/06/2025) : « Ce sont ces communautés de contrôle
    qui peuvent dire si un engagement ou une dette est tenue ».
  · CR 2026-S09 : « faire auditer par la communauté de contrôle les
    enregistrements avancés — si possible vérifier que les enregistrements
    duaux ont bien été effectués avec les autres entités ».

  LA RÈGLE INSTITUÉE (CONV-16)
  ----------------------------
  1. Chaque registre de communalité DÉSIGNE son instance de contrôle, par une
     désignation ARRÊTÉE (même logique que AX-7 et PR-37 : une désignation
     ratifiée ou non déclarée ne vaut pas).
  2. Le tiers d'une écriture duale entre A et B est l'instance de contrôle
     COMMUNE : désignée par les DEUX registres, qui n'est ni A ni B.
  3. Seule elle ARBITRE l'écart (PR-41 restreint : un tiers non lié mais non
     désigné n'arbitre pas), et elle peut CONSTATER la réalisation du
     maintien (PR-39 étendu : son constat vaut comme celui de l'autre teneur).
  4. Sans instance commune, l'écart reste inscrit, NON ARBITRABLE.

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne vérifie pas que l'instance est non liée : c'est la déclaration de
    l'investigation (PR-41, champ `lie`), supposée sincère.
  · Il ne dit pas comment l'instance est composée (financeurs, usagers,
    représentants — les exemples du corpus varient : « un cadre qui associe
    les financeurs / apporteurs de moyens », Trichon, 14/01/2025 ; « un
    comité du fleuve, du bien-être du fleuve », CR 2024-S24).
  · Il ne traite pas le désaccord ENTRE les deux registres sur l'instance :
    faute de désignation commune, rien n'est arbitré — c'est tout.
-/

import ProfReg.PR41_ArbitrageParUnTiers
import ProfReg.PR37_RegistreDuMilieu
import ProfReg.PR39_RealisationDuMaintien

namespace ProfRegPR43

open ProfRegPR35 (Entite)
open ProfRegPR41 (Investigation Issue StatutArbitre arbitrer tiersRecevable)
open ProfRegPR37 (ModeDeclaration)
open ProfRegPR39 (EtatResultat LigneRealisation Constat)
open ProfRegPR40 (StatutEcart)

/-! ## 1. La désignation de l'instance de contrôle -/

/-- Un registre (identifié par son teneur) désigne son instance de contrôle. -/
structure DesignationControle where
  registre : Entite
  instanceCtrl : Entite
  mode     : ModeDeclaration
  deriving DecidableEq, Repr

/-- La désignation par le registre `r` de l'instance `t` est valide. -/
def designe (ds : List DesignationControle) (r t : Entite) : Bool :=
  ds.any (fun d => d.registre == r && d.instanceCtrl == t && decide (d.mode = .arretee))

/-- **L'instance de contrôle commune** de A et B : désignée par les deux,
    ni A ni B. -/
def instanceCommune (ds : List DesignationControle) (a b t : Entite) : Bool :=
  designe ds a t && designe ds b t && !(t == a) && !(t == b)

/-! ## 2. L'arbitrage institué -/

/-- **Arbitrage institué** : une investigation n'est reçue que si son tiers
    est l'instance de contrôle commune ; elle passe alors par la règle de
    PR-41 (qui exclut encore le tiers lié). -/
def arbitrerInstitue (ds : List DesignationControle) (s : StatutEcart)
    (inv : Option Investigation) (a b : Entite) : StatutArbitre :=
  match inv with
  | none   => .nonArbitre s
  | some i => if instanceCommune ds a b i.tiers then arbitrer s (some i) a b
              else .nonArbitre s

/-- **Constat institué** (PR-39 étendu) : vaut constat celui de l'autre
    teneur `b`, ou celui de l'instance de contrôle commune. -/
def etatInstitue (ds : List DesignationControle) (l : LigneRealisation)
    (a b : Entite) : EtatResultat :=
  match l.constat with
  | none   => .attendu
  | some c =>
    if c.parTeneur == b || instanceCommune ds a b c.parTeneur then
      (if c.atteint then .constate else .conteste)
    else .attendu

/-! ## 3. Ce qui se démontre -/

/-- **Sans instance commune, rien n'est arbitré** — quel que soit le tiers,
    même non lié. -/
theorem sans_instance_commune_rien_n_est_arbitre (ds : List DesignationControle)
    (s : StatutEcart) (i : Investigation) (a b : Entite)
    (h : instanceCommune ds a b i.tiers = false) :
    arbitrerInstitue ds s (some i) a b = .nonArbitre s := by
  simp [arbitrerInstitue, h]

/-- **L'institution ne réintroduit pas le tiers lié** : même désignée par
    les deux registres, une instance déclarée liée n'arbitre pas. -/
theorem l_instance_liee_n_arbitre_pas (ds : List DesignationControle)
    (s : StatutEcart) (a b t : Entite) (iss : Issue) :
    arbitrerInstitue ds s (some ⟨t, true, iss⟩) a b = .nonArbitre s := by
  show (if instanceCommune ds a b t = true then arbitrer s (some ⟨t, true, iss⟩) a b
        else .nonArbitre s) = .nonArbitre s
  split
  · exact ProfRegPR41.un_tiers_lie_ne_tranche_pas s a b t iss
  · rfl

/-- **L'instance commune tranche toujours**, forme générale `[D-ED-37 —
    30/09/2026]` : une investigation conduite par l'instance commune,
    déclarée non liée, qui confirme, donne `confirmeParTiers` — quels que
    soient les registres, les désignations et le statut de départ. -/
theorem l_instance_commune_tranche_toujours (ds : List DesignationControle)
    (s : StatutEcart) (i : Investigation) (a b : Entite)
    (hc : instanceCommune ds a b i.tiers = true) (hl : i.lie = false)
    (hconf : i.issue = .confirme) :
    arbitrerInstitue ds s (some i) a b = .confirmeParTiers := by
  have h' := hc
  unfold instanceCommune at h'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h'
  obtain ⟨⟨⟨-, -⟩, ha⟩, hb⟩ := h'
  show (if instanceCommune ds a b i.tiers = true then arbitrer s (some i) a b else _) = _
  rw [if_pos hc]
  show (if tiersRecevable i a b = true then _ else _) = _
  have hr : tiersRecevable i a b = true := by
    unfold tiersRecevable; rw [ha, hb, hl]; rfl
  rw [if_pos hr, hconf]

/-! ## 4. Instance : l'entreprise, la rivière et le comité du fleuve -/

def entreprise : Entite := 2
def riviere    : Entite := 10
def comiteDuFleuve : Entite := 70
def bureauEtudes   : Entite := 71

/-- Les deux registres désignent le comité du fleuve (arrêté). -/
def dsCommun : List DesignationControle :=
  [⟨entreprise, comiteDuFleuve, .arretee⟩, ⟨riviere, comiteDuFleuve, .arretee⟩]
/-- Seule la rivière l'a désigné. -/
def dsUnilateral : List DesignationControle :=
  [⟨riviere, comiteDuFleuve, .arretee⟩]
/-- L'entreprise n'a fait que ratifier. -/
def dsRatifie : List DesignationControle :=
  [⟨entreprise, comiteDuFleuve, .ratifiee⟩, ⟨riviere, comiteDuFleuve, .arretee⟩]

/-- **PR-43 (1) — l'instance commune tranche ; un autre tiers non lié,
    non.** Le bureau d'études n'est ni partie ni lié, mais n'a été désigné
    par personne : son investigation est sans effet. -/
theorem seule_l_instance_commune_tranche :
    arbitrerInstitue dsCommun .conteste (some ⟨comiteDuFleuve, false, .confirme⟩)
        entreprise riviere = .confirmeParTiers
    ∧ arbitrerInstitue dsCommun .conteste (some ⟨bureauEtudes, false, .confirme⟩)
        entreprise riviere = .nonArbitre .conteste := by
  decide

/-- **PR-43 (2) — une désignation unilatérale ou ratifiée ne suffit pas.** -/
theorem la_designation_doit_etre_commune_et_arretee :
    arbitrerInstitue dsUnilateral .conteste (some ⟨comiteDuFleuve, false, .confirme⟩)
        entreprise riviere = .nonArbitre .conteste
    ∧ arbitrerInstitue dsRatifie .conteste (some ⟨comiteDuFleuve, false, .confirme⟩)
        entreprise riviere = .nonArbitre .conteste := by
  decide

/-- **PR-43 (3) — l'instance ne peut être partie.** Si l'entreprise se
    désignait elle-même, et la rivière aussi, elle ne serait pas instance
    commune. -/
theorem l_instance_ne_peut_etre_partie :
    instanceCommune [⟨entreprise, entreprise, .arretee⟩, ⟨riviere, entreprise, .arretee⟩]
      entreprise riviere entreprise = false := by
  decide

/-! ## 5. Le constat par l'instance de contrôle (PR-39 étendu) -/

open ProfRegPR39 (maintienR)

/-- **PR-43 (4) — l'instance commune peut constater la réalisation** : son
    constat vaut comme celui de l'autre teneur — « ces communautés de
    contrôle […] peuvent dire si un engagement ou une dette est tenue »
    (CR 2025-S25). Un tiers non désigné ne le peut pas. -/
theorem l_instance_de_controle_peut_constater :
    etatInstitue dsCommun ⟨2026, maintienR, some ⟨comiteDuFleuve, true⟩⟩ entreprise riviere
      = .constate
    ∧ etatInstitue dsCommun ⟨2026, maintienR, some ⟨bureauEtudes, true⟩⟩ entreprise riviere
      = .attendu
    ∧ etatInstitue dsCommun ⟨2026, maintienR, some ⟨entreprise, true⟩⟩ entreprise riviere
      = .attendu := by
  decide

/-- **Témoin discriminant** (R-7) de `instanceCommune`. -/
theorem instance_commune_temoin_discriminant :
    instanceCommune dsCommun entreprise riviere comiteDuFleuve = true
    ∧ instanceCommune dsUnilateral entreprise riviere comiteDuFleuve = false := by
  decide

end ProfRegPR43
