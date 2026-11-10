/-
  PR-17 · `regime_du_dispositif_declare`
  ======================================

  Nœud OPP du graphe : **l'opposabilité est un seuil, pas un état.**

  CE QU'IL ÉTABLIT
  ----------------
  Un critère d'accès aux droits — taux de non-recours, sous-inclusion,
  exhaustivité réalisée — n'est BIEN FORMÉ que si le dispositif auquel
  on l'applique est en régime `infrastructure`. Appliqué à une
  expérimentation, il mesure le dispositif contre sa propre définition.

  LE RAISONNEMENT, EN UNE PHRASE
  ------------------------------
  Un taux de non-recours rapporte des recourants à une population
  d'AYANTS DROIT, définie par une norme opposable. Un dispositif
  expérimental pose LUI-MÊME son périmètre d'éligibilité. Le
  dénominateur n'est donc pas extérieur au numérateur :
  [RAISONNEMENT AUTORÉFÉRENTIEL].

  ANCRAGE
  -------
  · Olivier De Schutter, *Éliminer la pauvreté en regardant au-delà de
    la croissance*, A/HRC/56/61, 1er mai 2024, §48 : le ciblage sous
    condition de ressources « aboutit régulièrement à une
    sous-inclusion dans les registres et à des taux élevés de
    non-recours aux prestations ». [VÉRIFIÉ sur source primaire]
  · Le point d'application est datable : c'est le seuil S3 de la note
    de cadrage Action 8 (RADIS, 1er septembre 2026) — « à quel moment
    le dispositif cesse d'être un service pour devenir une obligation
    portée par le territoire », mesuré en actes de reconnaissance
    opposables.
  · Versé en MRC_v5.6_NT-G7_Justice.md §3.1bis le 8 septembre 2026.

  ⚠️ RÈGLE DE RÉDACTION (NT-ARCH §8octies-bis ; dépliages : §8ter-bis, D-13)
  -------------------------------------
  L'obligation est écrite comme CONDITION DE BONNE FORMATION, jamais
  comme hypothèse. Le théorème CONCLUT le régime exigé ; il ne le
  suppose pas. C'est ce qui distingue PR-17 des deux V10c retirés le
  7 septembre.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib, sans import.
-/

namespace ProfRegPR17

/-! ## 1. Les deux régimes, et le défaut de déclaration -/

/-- Le régime du dispositif inscrit. `nonDeclare` est la valeur par
    défaut : le silence n'est pas une permission (§3). -/
inductive RegimeDispositif where
  | experimentation
  | infrastructure
  | nonDeclare
deriving DecidableEq, Repr

/-- D'où vient le dénominateur d'un critère d'accès aux droits. -/
inductive SourceDuDenominateur where
  /-- Population d'ayants droit définie par une norme opposable,
      **extérieure** au dispositif. -/
  | normeOpposable
  /-- Périmètre d'éligibilité **posé par le dispositif lui-même**. -/
  | perimetreDuDispositif
deriving DecidableEq, Repr

structure Dispositif where
  nom : String
  regime : RegimeDispositif

/-! ## 2. Le seul dénominateur disponible, selon le régime

Ce n'est pas une hypothèse ajoutée : c'est la définition des deux
régimes. Un dispositif est en régime `infrastructure` **précisément
quand** le droit qu'il sert est opposable indépendamment de lui —
donc quand une population d'ayants droit existe hors de lui.

`nonDeclare` est rangé du côté du périmètre auto-posé **par
prudence**, pas par symétrie : en l'absence de déclaration, on ne
peut pas établir qu'une norme opposable existe. -/

def denominateurDisponible : RegimeDispositif → SourceDuDenominateur
  | .infrastructure  => .normeOpposable
  | .experimentation => .perimetreDuDispositif
  | .nonDeclare      => .perimetreDuDispositif

/-- **Condition de bonne formation d'un critère d'accès aux droits.**
    Le dénominateur disponible doit être une norme opposable. -/
def CritereAccesBienForme (d : Dispositif) : Prop :=
  denominateurDisponible d.regime = SourceDuDenominateur.normeOpposable

/-! ## 3. Les théorèmes -/

/-- **PR-17.** Un critère d'accès aux droits bien formé **conclut** que
    le dispositif est en régime `infrastructure`.

    Le régime n'est pas supposé : il est déduit de la bonne formation
    du critère. -/
theorem regime_du_dispositif_declare (d : Dispositif)
    (h : CritereAccesBienForme d) :
    d.regime = RegimeDispositif.infrastructure := by
  unfold CritereAccesBienForme at h
  cases hr : d.regime with
  | infrastructure => rfl
  | experimentation => rw [hr] at h; simp [denominateurDisponible] at h
  | nonDeclare => rw [hr] at h; simp [denominateurDisponible] at h

/-- Corollaire opératoire : sur une expérimentation, le critère
    d'accès aux droits **n'est pas bien formé**. Ce n'est pas une
    interdiction morale, c'est un défaut de forme. -/
theorem experimentation_ne_supporte_pas_le_critere (d : Dispositif)
    (h : d.regime = RegimeDispositif.experimentation) :
    ¬ CritereAccesBienForme d := by
  intro hbf
  rw [regime_du_dispositif_declare d hbf] at h
  exact absurd h (by simp)

/-- **Le silence ne vaut pas permission.** Un dispositif dont le régime
    n'est pas déclaré ne supporte pas davantage le critère qu'une
    expérimentation. La valeur par défaut refuse ; elle n'autorise pas. -/
theorem nonDeclare_ne_vaut_pas_permission (d : Dispositif)
    (h : d.regime = RegimeDispositif.nonDeclare) :
    ¬ CritereAccesBienForme d := by
  intro hbf
  rw [regime_du_dispositif_declare d hbf] at h
  exact absurd h (by simp)

/-! ## 4. Le test de non-vacuité

Un théorème qui refuserait tout serait creux — c'est le défaut qui a
fait retirer cinq théorèmes du set le 7 septembre. PR-17 **trie** :
il admet un cas et en refuse deux. -/

def caisseExperimentale : Dispositif :=
  { nom := "caisse commune de l'alimentation (expérimentation)"
  , regime := RegimeDispositif.experimentation }

def droitOpposable : Dispositif :=
  { nom := "prestation ouverte par une norme opposable"
  , regime := RegimeDispositif.infrastructure }

/-- Le critère est bien formé sur un dispositif d'infrastructure.
    PR-17 n'interdit pas la mesure du non-recours : il la **situe**. -/
theorem PR17_admet_l_infrastructure : CritereAccesBienForme droitOpposable := by
  simp [CritereAccesBienForme, denominateurDisponible, droitOpposable]

/-- Et il la refuse sur l'expérimentation. Les deux ensemble
    établissent que PR-17 discrimine. -/
theorem PR17_refuse_l_experimentation : ¬ CritereAccesBienForme caisseExperimentale :=
  experimentation_ne_supporte_pas_le_critere caisseExperimentale rfl

/-! ## 5. Gardes -/

/-- Une **mesure interne** rapporte des participants au périmètre que
    le dispositif s'est donné. Son dénominateur est celui que le
    dispositif fournit — ce qui la rend bien formée là, précisément,
    où le critère d'accès ne l'est pas. -/
def MesureInterneBienFormee (d : Dispositif) : Prop :=
  denominateurDisponible d.regime = SourceDuDenominateur.perimetreDuDispositif

/-- **PR-17 ne juge pas le dispositif et n'interdit pas de le mesurer.**
    Sur la même expérimentation, la mesure interne est bien formée et
    le critère d'accès ne l'est pas. Ce qui est refusé est le
    **rapport à une population d'ayants droit**, pas l'observation. -/
theorem PR17_n_interdit_pas_la_mesure :
    MesureInterneBienFormee caisseExperimentale
    ∧ ¬ CritereAccesBienForme caisseExperimentale :=
  ⟨by simp [MesureInterneBienFormee, denominateurDisponible, caisseExperimentale],
   PR17_refuse_l_experimentation⟩

/-- Et les deux notions ne coïncident pas : sur un dispositif
    d'infrastructure, c'est l'inverse. Sans cet énoncé, la précédente
    se lirait comme si la mesure interne était toujours la bonne. -/
theorem les_deux_mesures_ne_coincident_pas :
    ¬ MesureInterneBienFormee droitOpposable
    ∧ CritereAccesBienForme droitOpposable :=
  ⟨by simp [MesureInterneBienFormee, denominateurDisponible, droitOpposable],
   PR17_admet_l_infrastructure⟩

/-! [C-5 — RETIRÉ LE 28/09/2026, décision du porteur] `PR17_ne_produit_pas_la_bascule`
    énonçait, sous `regime = experimentation`, que `regime ≠ infrastructure` :
    distinction de deux constructeurs, vraie de tout dispositif (forme 1). Le nom
    annonçait plus que l'énoncé. La délimitation reste en prose : PR-17 constate
    le régime déclaré ; le franchissement (seuil S3) est un fait institutionnel
    qu'aucun théorème du fichier ne produit. Garde de non-régression déclarée : ne pas réintroduire ce théorème sous un autre nom. -/

end ProfRegPR17
