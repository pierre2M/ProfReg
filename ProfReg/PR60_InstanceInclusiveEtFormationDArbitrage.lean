/-
  PR-60 · L'instance de contrôle inclusive et la formation d'arbitrage
  ===================================================================
  Porteur : Pierre Musseau. Écrit le 10 novembre 2026, sur décision du
  porteur du même jour (fichier d'état, décision n° 60). Appui formel de
  CONV-16 révisée (Annexe §A.15.12) et de NT-G6 §2.1.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR43_InstanceDeControle`.

  LE PROBLÈME
  -----------
  PR-43 exige de l'instance de contrôle commune qu'elle ne soit « ni A ni
  B » (`instanceCommune`, `l_instance_ne_peut_etre_partie`). Le nom
  d'instance de contrôle vient de Rochfeld, Cornu & Martin 2021 ; la
  condition vient de l'audit (ISA 505, ISA 550 §10(b)). La source juridique
  ne la pose pas : les cercles se recouvrent — « la communauté délibérative
  (et, à nouveau, possiblement de contrôle) », « une communauté attributaire
  peut devenir une communauté de contrôle » (p. 82) — et l'inclusivité du
  cercle des « contrôleurs » mesure la communalité (p. 80). Exclure les
  teneurs de l'instance réduisait l'inclusivité que NT-G6 déclare instance
  par instance.

  CE QUE L'EXIGENCE D'INDÉPENDANCE GARDE DE JUSTE
  -----------------------------------------------
  Une partie ne tranche pas l'écart qui la concerne (PR-41,
  `tiersRecevable` ; PR-16, PR-18 : déclarant seul réfutant mal formé).
  L'exigence porte sur l'ACTE D'ARBITRAGE, non sur la COMPOSITION de
  l'instance.

  LA RÈGLE (CONV-16 révisée)
  -------------------------
  1. L'instance de contrôle est désignée par les deux registres (désignation
     arrêtée, PR-43 `designe`). Sa composition est déclarée et peut compter
     les teneurs : elle vérifie le registre et constate.
  2. La FORMATION D'ARBITRAGE d'un écart entre A et B est faite des membres
     de l'instance qui ne sont ni A, ni B, ni liés à l'un d'eux (récusation).
     Seule une investigation conduite par un membre de la formation est
     reçue ; PR-41 s'applique ensuite.
  3. Formation vide : l'écart reste inscrit, non arbitré (effet de CONV-16
     conservé).
  4. Le constat de réalisation (PR-39) peut être fait par un membre de
     l'instance, sauf par le teneur dont l'effort est constaté.

  RAPPORT À PR-43
  ---------------
  PR-43 n'est pas modifié (le contrôle `mrc-check` l'évalue). Il se lit
  désormais comme le cas d'une instance réduite à une seule entité, qui est
  alors sa propre formation : `pr43_est_le_cas_d_une_instance_a_un_seul_membre`.
  `l_instance_ne_peut_etre_partie` (graphie compilée conservée, Annexe
  §A.12) porte sur cette entité arbitre, non sur la composition.

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne vérifie pas qu'un membre déclaré non lié l'est : c'est une
    déclaration (champ `lie`), supposée sincère, comme dans PR-41.
  · Il ne dit pas comment la formation délibère quand elle compte plusieurs
    membres (majorité, unanimité) : une investigation au plus par ligne,
    conduite par l'un d'eux, comme dans PR-41.
  · Il ne dit pas qu'une instance inclusive est meilleure : il établit
    qu'elle est bien formée.
-/
import ProfReg.PR43_InstanceDeControle

namespace ProfRegPR60

open ProfRegPR35 (Entite)
open ProfRegPR41 (Investigation Issue StatutArbitre arbitrer tiersRecevable)
open ProfRegPR37 (ModeDeclaration)
open ProfRegPR39 (EtatResultat LigneRealisation Constat maintienR)
open ProfRegPR40 (StatutEcart)
open ProfRegPR43 (DesignationControle designe instanceCommune arbitrerInstitue)

/-! ## 1. La composition de l'instance -/

/-- Un membre déclaré de l'instance de contrôle. `lie` : lié à A ou à B au
    sens d'ISA 550 §10(b), déclaré. -/
structure Membre where
  personne : Entite
  lie      : Bool
  deriving DecidableEq, Repr

/-- La composition déclarée d'une instance de contrôle. -/
structure Composition where
  instanceCtrl : Entite
  membres      : List Membre
  deriving DecidableEq, Repr

/-- L'instance est désignée par les deux registres, par une désignation
    arrêtée. Aucune condition ne porte sur sa composition. -/
def instanceDesignee (ds : List DesignationControle) (a b : Entite) (c : Composition) : Bool :=
  designe ds a c.instanceCtrl && designe ds b c.instanceCtrl

/-! ## 2. La formation d'arbitrage -/

/-- Un membre peut trancher l'écart entre A et B : ni A, ni B, non lié. -/
def recevable (a b : Entite) (m : Membre) : Bool :=
  !(m.personne == a) && !(m.personne == b) && !m.lie

/-- **La formation d'arbitrage** : les membres de l'instance qui ne sont pas
    récusés. -/
def formation (c : Composition) (a b : Entite) : List Membre :=
  c.membres.filter (recevable a b)

/-- **Arbitrage par la formation.** Une investigation n'est reçue que si
    l'instance est désignée par les deux registres et que son tiers est
    membre de la formation ; PR-41 s'applique ensuite. -/
def arbitrerParFormation (ds : List DesignationControle) (c : Composition)
    (s : StatutEcart) (inv : Option Investigation) (a b : Entite) : StatutArbitre :=
  match inv with
  | none   => .nonArbitre s
  | some i =>
    if instanceDesignee ds a b c && (formation c a b).any (fun m => m.personne == i.tiers)
    then arbitrer s (some i) a b
    else .nonArbitre s

/-- **Le constat par l'instance** (PR-39 étendu) : l'autre teneur `b`, ou un
    membre de l'instance désignée qui n'est pas `a`. -/
def etatParInstance (ds : List DesignationControle) (c : Composition)
    (l : LigneRealisation) (a b : Entite) : EtatResultat :=
  match l.constat with
  | none   => .attendu
  | some k =>
    if k.parTeneur == b ||
       (instanceDesignee ds a b c && c.membres.any (fun m => m.personne == k.parTeneur)
         && !(k.parTeneur == a))
    then (if k.atteint then .constate else .conteste)
    else .attendu

/-! ## 3. Ce qui se démontre -/

/-- **La formation ne compte jamais une partie** : tout membre de la
    formation n'est ni A, ni B, et n'est pas déclaré lié. -/
theorem la_formation_ne_compte_pas_les_parties (c : Composition) (a b : Entite)
    (m : Membre) (h : m ∈ formation c a b) :
    m.personne ≠ a ∧ m.personne ≠ b ∧ m.lie = false := by
  simp only [formation, List.mem_filter, recevable, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at h
  exact ⟨h.2.1.1, h.2.1.2, h.2.2⟩

/-- **Formation vide, rien n'est arbitré** — même si l'instance est désignée
    par les deux registres. -/
theorem formation_vide_rien_n_est_arbitre (ds : List DesignationControle) (c : Composition)
    (s : StatutEcart) (i : Investigation) (a b : Entite) (h : formation c a b = []) :
    arbitrerParFormation ds c s (some i) a b = .nonArbitre s := by
  simp [arbitrerParFormation, h]

/-- **Sans désignation par les deux registres, rien n'est arbitré.** -/
theorem sans_designation_commune_rien_n_est_arbitre (ds : List DesignationControle)
    (c : Composition) (s : StatutEcart) (i : Investigation) (a b : Entite)
    (h : instanceDesignee ds a b c = false) :
    arbitrerParFormation ds c s (some i) a b = .nonArbitre s := by
  simp [arbitrerParFormation, h]

/-- **Un tiers déclaré lié n'arbitre pas**, même membre de l'instance. -/
theorem un_membre_lie_n_arbitre_pas (ds : List DesignationControle) (c : Composition)
    (s : StatutEcart) (a b t : Entite) (iss : Issue) :
    arbitrerParFormation ds c s (some ⟨t, true, iss⟩) a b = .nonArbitre s := by
  show (if _ then arbitrer s (some ⟨t, true, iss⟩) a b else _) = _
  split
  · exact ProfRegPR41.un_tiers_lie_ne_tranche_pas s a b t iss
  · rfl

/-- **PR-43 est le cas d'une instance à un seul membre**, elle-même : son
    arbitrage par la formation est celui de PR-43. -/
theorem pr43_est_le_cas_d_une_instance_a_un_seul_membre (ds : List DesignationControle)
    (s : StatutEcart) (i : Investigation) (a b : Entite) :
    arbitrerParFormation ds ⟨i.tiers, [⟨i.tiers, false⟩]⟩ s (some i) a b
      = arbitrerInstitue ds s (some i) a b := by
  have hself : (i.tiers == i.tiers) = true := decide_eq_true rfl
  unfold arbitrerParFormation arbitrerInstitue instanceDesignee instanceCommune formation recevable
  cases ha : designe ds a i.tiers <;> cases hb : designe ds b i.tiers <;>
    cases h1 : (i.tiers == a) <;> cases h2 : (i.tiers == b) <;>
    simp only [List.filter, List.any, ha, hb, h1, h2, hself, Bool.not_false, Bool.not_true, Bool.and_true,
      Bool.and_false, Bool.or_false] <;> rfl

/-! ## 4. Instance : l'entreprise, la rivière et un comité qui les compte -/

open ProfRegPR43 (entreprise riviere comiteDuFleuve bureauEtudes dsCommun)

def hydrologue      : Entite := 72
def salarieEntreprise : Entite := 73

/-- Le comité du fleuve, désigné par les deux registres (`dsCommun`), compte
    l'entreprise, la rivière (par son écrivant), un salarié de l'entreprise
    déclaré lié, et une hydrologue non liée. -/
def comiteInclusif : Composition :=
  ⟨comiteDuFleuve, [⟨entreprise, false⟩, ⟨riviere, false⟩, ⟨salarieEntreprise, true⟩,
    ⟨hydrologue, false⟩]⟩

/-- **PR-60 (1) — l'instance peut compter les teneurs** : désignée par les
    deux registres, elle compte A et B parmi ses membres. -/
theorem l_instance_peut_compter_les_teneurs :
    instanceDesignee dsCommun entreprise riviere comiteInclusif = true
    ∧ comiteInclusif.membres.any (fun m => m.personne == entreprise) = true
    ∧ comiteInclusif.membres.any (fun m => m.personne == riviere) = true := by
  decide

/-- **PR-60 (2) — seule la formation tranche** : l'hydrologue tranche ;
    l'entreprise, la rivière et le salarié lié, membres de l'instance, non ;
    le bureau d'études, non membre, non plus. -/
theorem seule_la_formation_tranche :
    arbitrerParFormation dsCommun comiteInclusif .conteste
        (some ⟨hydrologue, false, .confirme⟩) entreprise riviere = .confirmeParTiers
    ∧ arbitrerParFormation dsCommun comiteInclusif .conteste
        (some ⟨entreprise, false, .confirme⟩) entreprise riviere = .nonArbitre .conteste
    ∧ arbitrerParFormation dsCommun comiteInclusif .conteste
        (some ⟨riviere, false, .infirme⟩) entreprise riviere = .nonArbitre .conteste
    ∧ arbitrerParFormation dsCommun comiteInclusif .conteste
        (some ⟨salarieEntreprise, false, .confirme⟩) entreprise riviere = .nonArbitre .conteste
    ∧ arbitrerParFormation dsCommun comiteInclusif .conteste
        (some ⟨bureauEtudes, false, .confirme⟩) entreprise riviere = .nonArbitre .conteste := by
  decide

/-- **PR-60 (3) — une instance faite des seules parties n'arbitre pas** :
    sa formation est vide ; l'écart reste inscrit. -/
theorem une_instance_des_seules_parties_n_arbitre_pas :
    formation ⟨comiteDuFleuve, [⟨entreprise, false⟩, ⟨riviere, false⟩]⟩ entreprise riviere = []
    ∧ arbitrerParFormation dsCommun ⟨comiteDuFleuve, [⟨entreprise, false⟩, ⟨riviere, false⟩]⟩
        .conteste (some ⟨entreprise, false, .confirme⟩) entreprise riviere
        = .nonArbitre .conteste := by
  decide

/-- **PR-60 (4) — un membre de l'instance peut constater**, sauf le teneur
    dont l'effort est constaté. -/
theorem un_membre_peut_constater_sauf_l_interesse :
    etatParInstance dsCommun comiteInclusif ⟨2026, maintienR, some ⟨hydrologue, true⟩⟩
        entreprise riviere = .constate
    ∧ etatParInstance dsCommun comiteInclusif ⟨2026, maintienR, some ⟨riviere, true⟩⟩
        entreprise riviere = .constate
    ∧ etatParInstance dsCommun comiteInclusif ⟨2026, maintienR, some ⟨entreprise, true⟩⟩
        entreprise riviere = .attendu
    ∧ etatParInstance dsCommun comiteInclusif ⟨2026, maintienR, some ⟨bureauEtudes, true⟩⟩
        entreprise riviere = .attendu := by
  decide

/-- **Témoin discriminant** (R-7) de `formation` : avec l'hydrologue, la
    formation n'est pas vide ; sans elle, elle l'est. -/
theorem formation_temoin_discriminant :
    formation comiteInclusif entreprise riviere = [⟨hydrologue, false⟩]
    ∧ formation ⟨comiteDuFleuve, [⟨entreprise, false⟩, ⟨riviere, false⟩,
        ⟨salarieEntreprise, true⟩]⟩ entreprise riviere = [] := by
  decide

end ProfRegPR60
