/-
  PR-23 · `BienFormee_ne_borne_pas_le_maintien`
  =============================================

  **Appui formel de CONV-11** (Annexe méthodologique §A.15.4, NT-ARCH
  §8.5.3bis), actée le 8 septembre 2026 avec la décision 3 de 12ter.

  CE QUE CE FICHIER NE FAIT PAS, ET C'EST LE POINT
  ------------------------------------------------
  **Il ne démontre pas CONV-11.** Une obligation ne se démontre pas,
  elle se déclare — c'est le motif de CONV-1 à CONV-4 et de CONV-9.
  Écrire « toute écriture bien formée déclare son mouvement de
  maintien » serait vrai par le type, donc creux ; l'écrire avec
  l'hypothèse « bien formée », sans témoins (§8ter-bis, R-2), serait la
  **forme 3** de §8ter, celle qui
  a mordu son auteur le matin même (§8quater).

  Ce fichier fait ce que PR-10 §7 fait pour CONV-9 : il **motive** et il
  **borne**.

  TROIS RÉSULTATS
  ---------------
  · §2 LE TROU — une écriture typée `e`, parfaitement bien formée au
    sens actuel, dont le mouvement de maintien n'est pas inscrit. **Le
    trou que CONV-11 ferme est exhibé, non postulé.**

  · §3 LA MORSURE — deux dettes d'écarts différents produisent **la même
    écriture** quand le maintien n'est pas inscrit ; et
    `priorite_sans_assiette` en tire la conséquence opératoire :
    R-PRIORITE-CREANCIERS n'est **pas évaluable**. C'est le seul
    résultat du fichier qui ait un contenu propre.

  · §4 LA GARDE — CONV-11 est satisfaite **sans registre financier**.
    Elle ne réintroduit pas le critère du bilan que le porteur a écarté
    le 8 septembre.

  DEUX PRÉCAUTIONS DE MODÉLISATION
  --------------------------------
  (a) Le type des **registres est un paramètre**, jamais une
      énumération close — leçon de PR-22
      (`enumeration_close_exclut_un_collectif`). L'énumération
      `RegistreEx` du §4 ne sert qu'à instancier un exemple.
  (b) Aucune chaîne de caractères, aucun réel : le contrôle des neuf
      `Classical.choice` doit rester à neuf. Leçon de PR-20, où la
      comparaison de littéraux `String` avait fait sonner le contrôle.

  `[RÉSERVE DE MODÈLE]` `Situation`, `Ecriture` et `ecart` sont **mes
  structures**. C'est la réserve du §2quinquies du graphe : un
  contre-exemple ne vaut que ce que vaut la fidélité de son modèle. Si
  l'écart modélisé ici n'est pas celui du registre, les théorèmes du §3
  sont vrais et hors sujet.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib, sans import.
-/

namespace ProfRegPR23

/-! ## 1. Le modèle

Réduit à ce que CONV-11 met en jeu : un typage, un apporteur d'effort,
le montant que l'écriture porte, une éventuelle mention en langue
naturelle, et une éventuelle **inscription structurée** du mouvement de
maintien. -/

/-- Le typage de l'écriture. `nonDeclare` est ce que la bonne formation
    actuelle refuse — c'est elle, et rien d'autre. -/
inductive Typage where
  | e           -- effort reçu
  | d           -- résultat rendu
  | nonDeclare
  deriving DecidableEq, Repr

/-- L'inscription structurée du mouvement de maintien : les cinq champs
    exigés par CONV-11.

    `R` — le type des registres — est un **paramètre**. Rien ici ne
    suppose que les registres soient énumérables, ni qu'il y en ait
    deux, ni lesquels. -/
structure InscriptionMaintien (A R K : Type) where
  /-- Qui déclare. Patron de `porteurDeLaDeclaration` (PR-18). -/
  porteur  : A
  /-- **Le registre qui porte la contrepartie**, nommé sur l'écriture. -/
  registre : R
  /-- Le solde — ce sans quoi aucun écart ne se calcule. -/
  solde    : Nat
  /-- L'horizon. -/
  horizon  : Nat
  /-- Le critère de vérification. Non dérivable des autres champs :
      champ déclaré légitime au sens de `PR21_ne_condamne_pas_les_champs_declares`. -/
  critere  : K

structure Ecriture (A R K : Type) where
  typage    : Typage
  apporteur : A
  /-- Ce que l'écriture porte au titre de l'exercice. -/
  montant   : Nat
  /-- Une mention en langue naturelle est-elle présente ? Une glose
      **n'a aucun champ** : c'est tout ce que le modèle en retient, et
      c'est exactement ce qui la disqualifie (§4). -/
  glose     : Bool
  maintien  : Option (InscriptionMaintien A R K)

variable {A R K : Type}

/-- **La bonne formation actuelle**, avant CONV-11 : le typage est
    déclaré. Patron de R0-bis (Annexe §A.14.3) — un prédicat décidable
    sur l'inscription seule, qui ne juge pas le fond. -/
def BienFormeeActuelle (ec : Ecriture A R K) : Prop :=
  ec.typage ≠ Typage.nonDeclare

/-- Ce que CONV-11 exige en plus. -/
def SatisfaitCONV11 (ec : Ecriture A R K) : Prop :=
  ec.maintien ≠ none

/-! ## 2. Le trou — et il est exhibé, non postulé

Patron de `BienFormee_ne_borne_pas_le_quintuplet` (PR-10 §7). -/

/-- **PR-23 (1).** Il existe une écriture typée `e`, **parfaitement bien
    formée au sens actuel**, dont le mouvement de maintien n'est pas
    inscrit.

    **CONV-11 ferme donc un trou réel.** Sans cet énoncé, l'obligation
    serait motivée par une intuition ; avec lui, elle l'est par un
    théorème. -/
theorem BienFormee_ne_borne_pas_le_maintien (a : A) :
    ∃ ec : Ecriture A R K,
      ec.typage = Typage.e ∧ BienFormeeActuelle ec ∧ ¬ SatisfaitCONV11 ec := by
  refine ⟨{ typage := Typage.e, apporteur := a, montant := 0
          , glose := false, maintien := none }, rfl, ?_, ?_⟩
  · unfold BienFormeeActuelle; intro h; exact Typage.noConfusion h
  · unfold SatisfaitCONV11; intro h; exact h rfl

/-- **Et l'obligation n'est pas impossible à tenir.** Sans cet énoncé,
    CONV-11 pourrait être vide — une condition que rien ne satisfait est
    un refus déguisé, non une obligation. -/
theorem CONV11_est_satisfiable (a : A) (r : R) (k : K) :
    ∃ ec : Ecriture A R K,
      ec.typage = Typage.e ∧ BienFormeeActuelle ec ∧ SatisfaitCONV11 ec := by
  refine ⟨{ typage := Typage.e, apporteur := a, montant := 0, glose := false
          , maintien := some ⟨a, r, 0, 1, k⟩ }, rfl, ?_, ?_⟩
  · unfold BienFormeeActuelle; intro h; exact Typage.noConfusion h
  · unfold SatisfaitCONV11; intro h; cases h

/-! ## 3. La morsure — sans inscription, la règle de priorité n'a pas
d'assiette

R-PRIORITE-CREANCIERS n'opère pas sur ce qui a été payé, mais sur
**l'écart entre le dû et le payé** (Annexe K §K.6.3, NT-ARCH §8.5.3bis).
Un écart ne se lit qu'entre deux grandeurs inscrites. -/

/-- Une situation de dette : ce qui est dû au titre du maintien sur la
    période, et ce qui a été effectivement engagé. -/
structure Situation where
  du   : Nat
  paye : Nat
  deriving DecidableEq, Repr

/-- L'écart. La soustraction de `Nat` est tronquée : un sur-financement
    donne un écart nul, ce qui est la lecture voulue. -/
def ecart (s : Situation) : Nat := s.du - s.paye

/-- L'écriture produite d'une situation **sans inscription du
    maintien** : elle ne porte que ce qui a été payé. -/
def ecritureSansMaintien (a : A) (s : Situation) : Ecriture A R K :=
  { typage := Typage.e, apporteur := a, montant := s.paye
  , glose := true, maintien := none }

/-- **PR-23 (2) — le résultat central.** Deux situations de dette
    d'**écarts différents** produisent **exactement la même écriture**
    quand le maintien n'est pas inscrit.

    Ce n'est pas une perte de précision : c'est une **non-identifiabilité**.
    Aucun tiers, si diligent soit-il, ne peut distinguer les deux
    situations à partir du registre. -/
theorem deux_dettes_distinctes_meme_ecriture (a : A) :
    ∃ s₁ s₂ : Situation,
      ecart s₁ ≠ ecart s₂
      ∧ (ecritureSansMaintien a s₁ : Ecriture A R K) = ecritureSansMaintien a s₂ := by
  refine ⟨⟨10, 4⟩, ⟨7, 4⟩, ?_, rfl⟩
  decide

/-- Ce qu'un tiers peut lire de l'écart sur l'écriture seule. -/
def ecartLisible (ec : Ecriture A R K) : Option Nat :=
  match ec.maintien with
  | some m => some m.solde
  | none   => none

/-- **La glose ne rend rien lisible.** L'écart lisible ne dépend **que**
    du mouvement de maintien : deux écritures s'accordant sur lui
    donnent la même lecture, quoi que dise leur mention en langue
    naturelle et quel que soit leur montant.

    C'est la formalisation exacte de « la glose ne vaut pas
    inscription » — et elle vaut quel que soit le document qui porte la
    glose, bilan compris. -/
theorem la_glose_ne_rend_rien_lisible (ec₁ ec₂ : Ecriture A R K)
    (h : ec₁.maintien = ec₂.maintien) :
    ecartLisible ec₁ = ecartLisible ec₂ := by
  unfold ecartLisible; rw [h]

/-- **Et la glose varie librement sans que rien ne change à la
    lecture.** Deux écritures dont la mention en langue naturelle
    diffère, dont le montant porté diffère, et dont **l'écart lisible et
    le verdict de priorité sont identiques** — parce que ni l'un ni
    l'autre ne dépendent de la glose.

    C'est le témoin que `la_glose_ne_rend_rien_lisible` n'exhibait pas :
    sans lui, l'énoncé précédent ne serait qu'une congruence. -/
theorem la_glose_varie_librement (a : A) :
    ∃ ec₁ ec₂ : Ecriture A R K,
      ec₁.glose ≠ ec₂.glose ∧ ec₁.montant ≠ ec₂.montant
      ∧ ecartLisible ec₁ = ecartLisible ec₂ := by
  refine ⟨{ typage := Typage.e, apporteur := a, montant := 31000
          , glose := true, maintien := none },
          { typage := Typage.e, apporteur := a, montant := 0
          , glose := false, maintien := none }, ?_, ?_, rfl⟩
  · intro h; exact Bool.noConfusion h
  · intro h; exact Nat.noConfusion h

/-- La règle de priorité, réduite à ce qu'elle demande : *y a-t-il un
    écart ?* Elle ne rend un verdict que si l'écart est lisible. -/
def prioriteMord (ec : Ecriture A R K) : Option Bool :=
  match ecartLisible ec with
  | some x => some (0 < x)
  | none   => none

/-- **PR-23 (3) — la conséquence opératoire.** Sans inscription du
    mouvement de maintien, **R-PRIORITE-CREANCIERS n'est pas
    évaluable** : la règle ne rend aucun verdict, ni positif ni négatif.

    Elle ne se trompe pas — elle n'a **pas d'assiette**. -/
theorem priorite_sans_assiette (ec : Ecriture A R K) (h : ec.maintien = none) :
    prioriteMord ec = none := by
  unfold prioriteMord ecartLisible; rw [h]

/-- Le solde lu, ou zéro. Projection auxiliaire du théorème suivant. -/
def soldeLu (ec : Ecriture A R K) : Nat :=
  match ec.maintien with
  | some m => m.solde
  | none   => 0

/-- L'écriture produite **avec** inscription du maintien : le solde
    porte l'écart. -/
def ecritureAvecMaintien (a : A) (r : R) (k : K) (s : Situation) :
    Ecriture A R K :=
  { typage := Typage.e, apporteur := a, montant := s.paye, glose := false
  , maintien := some ⟨a, r, ecart s, 1, k⟩ }

/-- **Et l'inscription lève la non-identifiabilité.** Deux situations
    d'écarts différents produisent alors deux écritures **distinctes** :
    ce que CONV-11 achète est exactement la distinction que le §3
    montrait perdue. -/
theorem le_maintien_separe_les_situations (a : A) (r : R) (k : K)
    (s₁ s₂ : Situation) (h : ecart s₁ ≠ ecart s₂) :
    (ecritureAvecMaintien a r k s₁ : Ecriture A R K)
      ≠ ecritureAvecMaintien a r k s₂ := by
  intro heq
  exact h (congrArg soldeLu heq)

/-- **Et la règle de priorité mord alors effectivement.** Sur une
    situation sous-financée, elle rend un verdict. -/
theorem priorite_mord_si_inscrite (a : A) (r : R) (k : K) (s : Situation)
    (h : s.paye < s.du) :
    prioriteMord (ecritureAvecMaintien a r k s : Ecriture A R K) = some true := by
  have h' : 0 < ecart s := by unfold ecart; omega
  unfold prioriteMord ecartLisible ecritureAvecMaintien
  exact congrArg some (decide_eq_true h')

/-! ## 4. La garde — le registre financier n'est pas requis

Le porteur a écarté, le 8 septembre 2026, le critère de **lieu dans les
états financiers** que portait la version 1 de la condition. Cette
section vérifie que CONV-11 ne le réintroduit pas.

L'énumération ci-dessous **n'est pas** le type des registres du modèle
(qui reste le paramètre `R`) : elle instancie un exemple. -/

inductive RegistreEx where
  | financier | communalite | extraFinancier
  deriving DecidableEq, Repr

/-- **PR-23 (4).** CONV-11 est satisfaite par une écriture dont le
    registre porteur **n'est pas** le registre financier — et elle l'est
    aussi bien par le registre de communalité que par un rapport
    extra-financier.

    *« Si A reconnaît une dette envers B et l'inscrit dans son registre
    de communalité avec la contrepartie, le solde, l'horizon, la
    condition doit être considérée comme remplie même si le régime
    comptable qu'applique A ne permet pas de traduire cette dette en
    chiffre dans le bilan financier. »* — décision de porteur,
    8 septembre 2026. -/
theorem CONV11_satisfaite_sans_registre_financier (a : A) (k : K) :
    ∀ r : RegistreEx,
      ∃ ec : Ecriture A RegistreEx K,
        SatisfaitCONV11 ec ∧ ∃ m, ec.maintien = some m ∧ m.registre = r := by
  -- [B-8, 28/09/2026] Hypothèse inerte `r ≠ financier` retirée (forme 2, invisible
  -- au linter) : l'énoncé vaut pour tout registre, donc en particulier sans le
  -- registre financier.
  intro r
  refine ⟨{ typage := Typage.e, apporteur := a, montant := 0, glose := false
          , maintien := some ⟨a, r, 3, 1, k⟩ }, ?_, ⟨a, r, 3, 1, k⟩, rfl, rfl⟩
  unfold SatisfaitCONV11; intro h; cases h

/-- **Et la glose ne la satisfait pas**, fût-elle abondante. Une mention
    sans champ propre laisse `maintien` vide, donc l'écart illisible
    (`la_glose_ne_rend_rien_lisible`) et la priorité sans assiette
    (`priorite_sans_assiette`). -/
theorem la_glose_ne_satisfait_pas_CONV11 (a : A) :
    ∃ ec : Ecriture A R K,
      ec.glose = true ∧ ¬ SatisfaitCONV11 ec ∧ ecartLisible ec = none := by
  refine ⟨{ typage := Typage.e, apporteur := a, montant := 31000
          , glose := true, maintien := none }, rfl, ?_, rfl⟩
  unfold SatisfaitCONV11; intro h; exact h rfl

/-! ## 5. Gardes — ce que PR-23 ne dit pas -/

/-- **PR-23 ne juge aucun montant.** Deux inscriptions de soldes
    différents satisfont l'une et l'autre CONV-11 : la condition porte
    sur la **forme** de l'inscription, jamais sur la justesse du
    chiffre. Même figure que `PR10_ne_juge_pas_l_usage_de_l_agregat`. -/
theorem PR23_ne_juge_aucun_montant (a : A) (r : R) (k : K) (x y : Nat) :
    ∃ ec₁ ec₂ : Ecriture A R K,
      SatisfaitCONV11 ec₁ ∧ SatisfaitCONV11 ec₂
      ∧ soldeLu ec₁ = x ∧ soldeLu ec₂ = y := by
  refine ⟨{ typage := Typage.e, apporteur := a, montant := 0, glose := false
          , maintien := some ⟨a, r, x, 1, k⟩ },
          { typage := Typage.e, apporteur := a, montant := 0, glose := false
          , maintien := some ⟨a, r, y, 1, k⟩ }, ?_, ?_, rfl, rfl⟩
  · unfold SatisfaitCONV11; intro h; cases h
  · unfold SatisfaitCONV11; intro h; cases h

/-- **PR-23 ne privilégie aucun registre.** Pour **tout** registre — le
    type est un paramètre, non une liste — il existe une écriture qui
    satisfait CONV-11 en le nommant. C'est la version paramétrique du
    §4, et elle évite l'erreur que PR-22 a démontrée : une énumération
    close exclut toujours quelqu'un. -/
theorem PR23_ne_privilegie_aucun_registre (a : A) (k : K) (r : R) :
    ∃ ec : Ecriture A R K, SatisfaitCONV11 ec ∧ soldeLu ec = 0
      ∧ ∃ m, ec.maintien = some m ∧ m.registre = r := by
  -- [B-10, 28/09/2026] Complété : `r` n'apparaissait pas dans la conclusion ; rien
  -- ne disait que l'écriture nomme `r`. Désormais elle le nomme.
  refine ⟨{ typage := Typage.e, apporteur := a, montant := 0, glose := false
          , maintien := some ⟨a, r, 0, 1, k⟩ }, ?_, rfl, ⟨a, r, 0, 1, k⟩, rfl, rfl⟩
  unfold SatisfaitCONV11; intro h; cases h

/-- **PR-23 n'affirme aucune dette.** Une écriture dont le solde est nul
    satisfait CONV-11 : l'obligation porte sur l'inscription du
    mouvement, non sur l'existence d'un impayé. Sans cette garde,
    CONV-11 se lirait comme une présomption de sous-financement. -/
theorem PR23_n_affirme_aucune_dette (a : A) (r : R) (k : K) :
    ∃ ec : Ecriture A R K,
      SatisfaitCONV11 ec ∧ prioriteMord ec = some false := by
  refine ⟨{ typage := Typage.e, apporteur := a, montant := 0, glose := false
          , maintien := some ⟨a, r, 0, 1, k⟩ }, ?_, rfl⟩
  unfold SatisfaitCONV11; intro h; cases h

/-- **PR-23 ne certifie pas le nommage du registre** — et il le
    démontre plutôt que de le concéder. Le champ `registre` est
    **libre** : deux écritures ne différant que par lui satisfont
    l'une et l'autre CONV-11, et rien dans le modèle ne vérifie que le
    nom désigne un registre existant.

    C'est la `[LACUNE DE COUVERTURE]` d'Annexe §A.15.4, écrite comme un
    théorème. Elle ne se ferme qu'en indexant L2 par une liste déclarée
    de registres (issue (b) de §A.14.10). -/
theorem PR23_ne_certifie_pas_le_nommage (a : A) (k : K) (r₁ r₂ : R) :
    ∃ ec₁ ec₂ : Ecriture A R K,
      SatisfaitCONV11 ec₁ ∧ SatisfaitCONV11 ec₂
      ∧ ecartLisible ec₁ = ecartLisible ec₂
      ∧ (∃ m₁ m₂, ec₁.maintien = some m₁ ∧ ec₂.maintien = some m₂
                  ∧ m₁.registre = r₁ ∧ m₂.registre = r₂) := by
  refine ⟨{ typage := Typage.e, apporteur := a, montant := 0, glose := false
          , maintien := some ⟨a, r₁, 5, 1, k⟩ },
          { typage := Typage.e, apporteur := a, montant := 0, glose := false
          , maintien := some ⟨a, r₂, 5, 1, k⟩ }, ?_, ?_, rfl,
          ⟨a, r₁, 5, 1, k⟩, ⟨a, r₂, 5, 1, k⟩, rfl, rfl, rfl, rfl⟩
  · unfold SatisfaitCONV11; intro h; cases h
  · unfold SatisfaitCONV11; intro h; cases h

/-- **Témoin discriminant direct** (R-7, 28/09/2026) de la lecture
    `la_glose_ne_rend_rien_lisible` : dès que le maintien est inscrit,
    `ecartLisible` rend l'**autre** valeur — `some`, l'écart de la situation —
    là où l'écriture sans maintien rend `none`. Remplace le témoin indirect par
    `prioriteMord` (table R-7, n° 30). -/
theorem ecart_lisible_temoin_discriminant (a : A) (r : R) (k : K) (s : Situation) :
    ecartLisible (ecritureAvecMaintien a r k s : Ecriture A R K) = some (ecart s)
    ∧ ecartLisible (ecritureSansMaintien a s : Ecriture A R K) = none :=
  ⟨rfl, rfl⟩

/-! ## 6. La structure complète de CONV-11 — D-ED-16, 30 septembre 2026

`[D-ED-16 — 30/09/2026, décision du porteur]` `[INCOHÉRENCE INTER-COUCHES —
niveau 0, levée]` CONV-11 (Annexe §A.15.4) exige une inscription structurée
« porteur, contrepartie, solde, horizon, critère de vérification » **et** que
l'écriture « nomme le registre qui la porte » : six éléments.
`InscriptionMaintien` (§1) en porte cinq — la **contrepartie** y manque, fondue
dans le registre — et `Maintien` de PR-37 (29/09) en portait cinq autres — le
**registre** y manquait. Dans les deux, le **solde** était un champ déclaré,
alors que ce fichier sait le calculer (`ecart`, §3).

`MaintienCONV11` porte les six éléments ; le solde **n'est plus un champ** :
il est l'écart de la `Situation` (dû − engagé), c'est-à-dire la « dette de
préservation » au sens CARE (Vuattoux, chap. 2 : « l'écart entre ce que
l'organisation devrait engager pour assurer ce maintien et ce qu'elle engage
effectivement »). `InscriptionMaintien` est conservée : elle devient la
**projection** de la structure complète, et les quatorze théorèmes ci-dessus
restent vrais sans être réécrits. -/

/-- **Le maintien au sens de CONV-11, complet.** -/
structure MaintienCONV11 (A R K : Type) where
  porteur      : A
  contrepartie : A
  /-- Le registre qui porte l'inscription. -/
  registre     : R
  /-- Ce qui est dû au titre du maintien, et ce qui a été engagé. -/
  situation    : Situation
  horizon      : Nat
  critere      : K

/-- **Le solde est calculé, jamais déclaré** : c'est l'écart de la situation. -/
def MaintienCONV11.solde (m : MaintienCONV11 A R K) : Nat := ecart m.situation

/-- La projection vers l'inscription du §1 : on perd la contrepartie, et le
    solde y est recopié **depuis le calcul**. -/
def MaintienCONV11.versInscription (m : MaintienCONV11 A R K) :
    InscriptionMaintien A R K :=
  ⟨m.porteur, m.registre, m.solde, m.horizon, m.critere⟩

/-- L'écriture qu'un maintien complet engendre : elle porte ce qui a été
    engagé, et le maintien projeté. -/
def ecritureDepuisCONV11 (a : A) (m : MaintienCONV11 A R K) : Ecriture A R K :=
  { typage := Typage.e, apporteur := a, montant := m.situation.paye, glose := false
  , maintien := some m.versInscription }

/-- **Compatibilité.** L'écriture engendrée par un maintien complet est
    exactement `ecritureAvecMaintien` du §3 : tout ce que PR-23 démontre de
    celle-ci (`le_maintien_separe_les_situations`, `priorite_mord_si_inscrite`,
    `ecart_lisible_temoin_discriminant`) vaut pour la structure complète. -/
theorem CONV11_complet_retrouve_PR23 (a c : A) (r : R) (k : K) (s : Situation) :
    (ecritureDepuisCONV11 a ⟨a, c, r, s, 1, k⟩ : Ecriture A R K)
      = ecritureAvecMaintien a r k s := rfl

/-- Un maintien complet satisfait CONV-11 au sens du §1. -/
theorem CONV11_complet_satisfait_CONV11 (a : A) (m : MaintienCONV11 A R K) :
    SatisfaitCONV11 (ecritureDepuisCONV11 a m) := by
  unfold SatisfaitCONV11 ecritureDepuisCONV11; intro h; cases h

/-- **Pourquoi six champs et non cinq.** Deux maintiens qui ne diffèrent que
    par la contrepartie ont la **même** projection : l'inscription du §1 ne
    sait pas envers qui le maintien est dû. -/
theorem la_projection_perd_la_contrepartie :
    ∃ m₁ m₂ : MaintienCONV11 Nat Nat Nat,
      m₁.contrepartie ≠ m₂.contrepartie ∧ m₁.versInscription = m₂.versInscription :=
  ⟨⟨0, 1, 0, ⟨100, 60⟩, 1, 0⟩, ⟨0, 2, 0, ⟨100, 60⟩, 1, 0⟩, by decide, rfl⟩

/-- **La dette de préservation est calculée.** Dû 100, engagé 60 : solde 40.
    Sur-financement (dû 50, engagé 80) : solde nul — la lecture voulue du §3,
    qui n'affirme aucune dette. Témoin de la lecture `MaintienCONV11.solde`. -/
theorem la_dette_de_preservation_est_calculee :
    (⟨0, 1, 0, ⟨100, 60⟩, 1, 0⟩ : MaintienCONV11 Nat Nat Nat).solde = 40
    ∧ (⟨0, 1, 0, ⟨50, 80⟩, 1, 0⟩ : MaintienCONV11 Nat Nat Nat).solde = 0 := by
  decide

end ProfRegPR23
