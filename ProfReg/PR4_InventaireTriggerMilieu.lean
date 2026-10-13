/-
  PR-4 · `inventaire_trigger_milieu`
  ==================================

  NT-ARCH §5.1 — INVENTAIRE-ASSETS-ACTIFS (amendement B2) :

  > Déclenchement : `regimeobligation = SYSTEMIQUE/HYBRIDE`, **OU**
  > `MILIEU_DEGRADE_PERSISTANT` (renvoi NT-G5), **OU**
  > `APPEL_IMMANENT_NON_ENTENDU` (renvoi NT-G2). […]
  > `InventaireNonVide = { l : List DID // l ≠ [] }`.
  > **Clôture interdite avec liste vide.**

  CE QUE PR-4 AJOUTE À `inventaire_nonempty_required`
  ----------------------------------------------------
  Le théorème déjà compilé (`V4Verification.lean`) dit que le **type**
  interdit la liste vide. Il ne dit rien de la **chaîne** : rien n'oblige
  un signal à produire la phase, ni la phase à produire l'inventaire.
  PR-4 porte sur la chaîne, et §3 en exhibe le trou.

  POURQUOI CE NŒUD N'EST PAS SUR LE CHEMIN DÉDUCTIF, ET COMPTE QUAND MÊME
  ------------------------------------------------------------------------
  Reclassé le 7 septembre comme **dépendance de traduction de PAL-1** :
  *« c'est lui qui fait entrer le signal du milieu dans la procédure ;
  si PAL-1 doit parler de collectifs attachés à des choses, PR-4 est le
  point où les choses entrent dans le modèle. »*

  §4 le démontre plutôt que de le redire : des trois déclencheurs, deux
  sont **déclarés par un acteur** et un seul est **constaté sur un
  état** — et c'est celui du milieu.

  `[RÉSERVE DE MODÈLE]` `Ecriture`, `declencheurActif` et `cloturable`
  sont mes structures. `InventaireNonVide` reprend la définition du set
  (`Primitives.lean`) plutôt que de l'importer, pour rester hors
  Mathlib ; c'est la même définition, à l'identique.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib, sans import.
-/

namespace ProfRegPR4

/-! ## 1. Le modèle -/

/-- Reprise littérale de `Primitives.lean` : `{ l : List String // l ≠ [] }`. -/
def InventaireNonVide := { l : List String // l ≠ [] }

/-- L'habitabilité du milieu, telle que NT-G5 la mesure. -/
inductive EtatHabitabilite where
  | viable | fragile | inhabitable
  deriving DecidableEq, Repr

/-- Le régime d'obligation, réduit à ce qui déclenche. -/
inductive RegimeObl where
  | actoriel | systemique | hybride
  deriving DecidableEq, Repr

/-- Une écriture, et ce que le registre en sait. -/
structure Ecriture where
  regime : RegimeObl
  /-- Deux intervalles de mesure : `MILIEU_DEGRADE_PERSISTANT` est
      *« état_habitabilité_milieu = FRAGILE/INHABITABLE sur 2
      intervalles »*. Le mot **persistant** est là : un seul intervalle
      ne déclenche pas. -/
  habitabilite₁ : EtatHabitabilite
  habitabilite₂ : EtatHabitabilite
  /-- Renvoi NT-G2. **Projection booléenne déclarée** (D-5-3, 28/09/2026) du
      signal F4 `APPEL_IMMANENT_NON_ENTENDU` (NT-ARCH §4.3, migré le 26/09) :
      `true` ssi `appel_immanent` non nul **et** `appel_entendu_milieu ∈
      {NON_ENTENDU, ENTENDU_ET_NON_ENTENDU}` ; `false` sur `ENTENDU`,
      `INDECIDABLE_ATTESTE` et `NONDECLARE`. La projection **perd** la
      distinction entre ces trois dernières valeurs : PR-4 ne dit rien de ce
      qui les sépare. Elle ne code pas l'indécidabilité en négation : sur
      `INDECIDABLE_ATTESTE`, le signal ne se lève pas (NT-G5 §3.1). -/
  appelImmanentNonEntendu : Bool
  /-- L'inventaire, s'il a été produit. -/
  inventaire : Option InventaireNonVide

def degrade : EtatHabitabilite → Bool
  | EtatHabitabilite.viable => false
  | _                       => true

/-- **`MILIEU_DEGRADE_PERSISTANT`** — calculé sur deux intervalles,
    jamais déclaré. -/
def milieuDegradePersistant (e : Ecriture) : Bool :=
  degrade e.habitabilite₁ && degrade e.habitabilite₂

def regimeDeclencheur : RegimeObl → Bool
  | RegimeObl.actoriel => false
  | _                  => true

/-- Les trois déclencheurs de la phase INVENTAIRE, en disjonction. -/
def phaseInventaireRequise (e : Ecriture) : Bool :=
  regimeDeclencheur e.regime || milieuDegradePersistant e || e.appelImmanentNonEntendu

/-- La clôture, telle que §5.1 la conditionne. -/
def cloturable (e : Ecriture) : Bool :=
  if phaseInventaireRequise e then e.inventaire.isSome else true

/-! ## 2. Le milieu déclenche, et la persistance est exigée -/

/-- **PR-4 (1).** Un milieu dégradé sur les deux intervalles déclenche
    la phase INVENTAIRE. C'est l'énoncé du set. -/
theorem milieu_degrade_persistant_declenche (e : Ecriture)
    (h : milieuDegradePersistant e = true) : phaseInventaireRequise e = true := by
  unfold phaseInventaireRequise
  rw [h]
  simp

/-- **PR-4 (2) — et un seul intervalle ne suffit pas.** La persistance
    n'est pas un ornement du nom : il existe une écriture dégradée sur
    un intervalle, viable sur l'autre, que le milieu **ne déclenche
    pas**. -/
theorem un_seul_intervalle_ne_declenche_pas :
    ∃ e : Ecriture, degrade e.habitabilite₁ = true
                  ∧ milieuDegradePersistant e = false := by
  refine ⟨⟨RegimeObl.actoriel, EtatHabitabilite.fragile, EtatHabitabilite.viable,
           false, none⟩, rfl, rfl⟩

/-! ## 3. La chaîne, et son trou -/

/-- **PR-4 (3).** Une écriture déclenchée et clôturable **porte** un
    inventaire, et cet inventaire est non vide — c'est le type qui
    l'assure, et c'est `inventaire_nonempty_required` réutilisé. -/
theorem cloture_declenchee_exhibe_un_inventaire_non_vide (e : Ecriture)
    (hd : phaseInventaireRequise e = true) (hc : cloturable e = true) :
    ∃ inv : InventaireNonVide, e.inventaire = some inv ∧ inv.val ≠ [] := by
  unfold cloturable at hc
  rw [if_pos hd] at hc
  cases hi : e.inventaire with
  | none => rw [hi] at hc; simp at hc
  | some inv => exact ⟨inv, rfl, inv.property⟩

/-- **PR-4 (4) — le trou, et il est le point de PR-4.** Le type
    `InventaireNonVide` interdit la liste vide ; **il n'oblige personne
    à produire un inventaire**. Il existe une écriture que le milieu
    déclenche et qui n'en porte aucun.

    `inventaire_nonempty_required` ne ferme donc pas la chaîne : il en
    ferme le dernier maillon. **C'est la clôture qui doit être
    interdite, et c'est une obligation, pas une propriété du type.** -/
theorem le_type_ne_produit_aucun_inventaire :
    ∃ e : Ecriture, phaseInventaireRequise e = true
                  ∧ e.inventaire = none
                  ∧ cloturable e = false := by
  refine ⟨⟨RegimeObl.actoriel, EtatHabitabilite.fragile, EtatHabitabilite.inhabitable,
           false, none⟩, rfl, rfl, rfl⟩

/-- **Et la clôture est effectivement refusée dans ce cas** — le refus
    est calculé, non déclaré (règle de §8sexies). -/
theorem cloture_interdite_sans_inventaire (e : Ecriture)
    (hd : phaseInventaireRequise e = true) (hi : e.inventaire = none) :
    cloturable e = false := by
  unfold cloturable
  rw [if_pos hd, hi]
  rfl

/-! ## 4. Ce que PR-4 fait entrer dans le modèle

Le résultat qui justifie le reclassement du 7 septembre. -/

/-- **PR-4 (5).** Des trois déclencheurs, deux se lisent sur ce qu'un
    acteur a **déclaré** — le régime d'obligation, l'appel immanent non
    entendu — et **un seul se calcule sur un état mesuré** : celui du
    milieu.

    On l'écrit sans détour : il existe une écriture dont **aucun champ
    déclaré** ne déclenche, et que le milieu déclenche pourtant.
    **C'est le point où les choses entrent dans le modèle**, et il n'y
    en a pas d'autre. -/
theorem le_milieu_declenche_sans_qu_aucun_acteur_ait_declare :
    ∃ e : Ecriture,
      regimeDeclencheur e.regime = false
      ∧ e.appelImmanentNonEntendu = false
      ∧ milieuDegradePersistant e = true
      ∧ phaseInventaireRequise e = true := by
  refine ⟨⟨RegimeObl.actoriel, EtatHabitabilite.inhabitable, EtatHabitabilite.fragile,
           false, none⟩, rfl, rfl, rfl, rfl⟩

/-! ## 5. Gardes -/

/-- **PR-4 ne privilégie aucun déclencheur.** Les trois sont en
    disjonction : chacun suffit, aucun n'est requis. Sans cette garde,
    le fichier se lirait comme si le milieu était le déclencheur
    principal. -/
theorem PR4_les_trois_declencheurs_suffisent_chacun (e : Ecriture) :
    (regimeDeclencheur e.regime = true → phaseInventaireRequise e = true)
  ∧ (milieuDegradePersistant e = true → phaseInventaireRequise e = true)
  ∧ (e.appelImmanentNonEntendu = true → phaseInventaireRequise e = true) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> unfold phaseInventaireRequise <;> rw [h] <;> simp

/-- **PR-4 ne juge pas le contenu de l'inventaire.** Deux inventaires
    non vides quelconques rendent la clôture également possible : la
    règle porte sur l'existence, jamais sur la pertinence des entités
    listées. -/
theorem PR4_ne_juge_pas_le_contenu (e : Ecriture) (i₁ i₂ : InventaireNonVide) :
    cloturable { e with inventaire := some i₁ }
      = cloturable { e with inventaire := some i₂ } := rfl

/-  **PR-4 ne dit pas que le milieu a été entendu** — garde déclarée, non prouvée.
    Le déclenchement par le milieu est une conséquence de l'état mesuré ; il ne
    suppose ni ne produit aucune reconnaissance.

    [D-5-2 — RETIRÉ LE 28/09/2026, décision du porteur ; audit A-5] Le théorème
    `PR4_ne_formalise_pas_l_appel_entendu` concluait
    `phaseInventaireRequise e = true ∧ e.appelImmanentNonEntendu = e.appelImmanentNonEntendu` :
    le second conjoint est `x = x` (forme 1), et le premier est exactement
    `milieu_degrade_persistant_declenche`. Sa docstring disait
    `appel_entendu_milieu` « un autre champ » : c'est faux depuis la migration
    du 26/09 — le champ `appelImmanentNonEntendu` en est la projection
    booléenne, déclarée ci-dessus. L'indépendance du déclenchement par le
    milieu est démontrée par `le_milieu_declenche_sans_qu_aucun_acteur_ait_declare`.
    Patron du retrait : `PR24_ne_conclut_pas_P1` (27/09). -/

/-- **Témoin discriminant** (R-7, 28/09/2026) des lectures de
    `phaseInventaireRequise` et de `cloturable` — `milieu_degrade_persistant_declenche`,
    `cloture_interdite_sans_inventaire`, `PR4_les_trois_declencheurs_suffisent_chacun`,
    `PR4_ne_juge_pas_le_contenu` : (1) une écriture sans déclencheur ne requiert pas
    la phase et reste clôturable ; (2) une écriture déclenchée **et** inventoriée est
    clôturable. -/
theorem PR4_temoin_discriminant :
    (∃ e : Ecriture, phaseInventaireRequise e = false ∧ cloturable e = true)
    ∧ (∃ e : Ecriture, phaseInventaireRequise e = true ∧ cloturable e = true) :=
  ⟨⟨⟨RegimeObl.actoriel, EtatHabitabilite.fragile, EtatHabitabilite.viable, false, none⟩, rfl, rfl⟩,
   ⟨⟨RegimeObl.actoriel, EtatHabitabilite.fragile, EtatHabitabilite.fragile, false, some ⟨["did:mrc:x"], List.cons_ne_nil _ _⟩⟩, rfl, rfl⟩⟩

end ProfRegPR4
