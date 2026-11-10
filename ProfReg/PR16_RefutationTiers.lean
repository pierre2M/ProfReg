/-
  PR-16 · `refutation_exige_un_tiers` — formalisation du maillon L3
  =================================================================

  Ce théorème ne vient pas du programme PR-1 → PR-10 : c'est un
  **énoncé nouveau**, proposé comme amendement, et il ferme un maillon
  que le graphe portait depuis le 6 septembre 2026 sans aucun appui.

  Pourquoi il est devenu exigible :
    · `ProfReg/PR8_RefutationPratique.lean`, théorème
      `PR8_ne_juge_pas_la_praticabilite`, exhibe une inscription
      parfaitement bien formée dont la condition de réfutation est
      « réfutable par le seul porteur, à huis clos ». Textuellement
      présente, réfutable par personne. **PR-8 garantit une
      inscription, pas une possibilité de contester.**
    · L3 est exactement cet écart.

  Ancrage :
    · Helen E. Longino, *Science as Social Knowledge: Values and
      Objectivity in Scientific Inquiry*, Princeton University Press,
      1990 — les quatre conditions de la critique transformative,
      ch. 4, p. 76 : (1) voies reconnues de critique ; (2) standards
      partagés ; (3) réponse de la communauté ; (4) égalité de
      l'autorité intellectuelle. [SOURCE PRIMAIRE LUE — ch. 4,
      p. 72-79, le 28/09/2026 ; voir
      `ProfReg/Fiche_Axiome_A14_Longino_Objectivite_Sociale_2026-09-28.md`
      (axiome AX-14). Ce fichier formalise la transposition d'AX-14, il ne
      prouve pas AX-14.]
      [CORRIGÉ LE 29/09/2026 — A14-a : l'ancrage était une citation au
      second degré (SEP), et la numérotation des conditions était
      fausse (reprise = 3, non 2 ; standards = 2, non 3).]
    · `L3_Refutabilite_Inspectabilite_2026-09-07.md`.

  ⚠️ Ce fichier NE s'appuie PAS sur Popper. La falsifiabilité
  poppérienne est une propriété d'ÉNONCÉS, définie par leur forme
  logique ; L3 porte sur des INSCRIPTIONS et exige une procédure
  disponible. Les deux notions partagent un mot, non un régime.
  Emprunter à l'une la légitimité de l'autre serait un
  [DÉCOUPLAGE DE RÉGIMES].

  Porteur : Pierre Musseau. Écrit le 7 septembre 2026.
  Lean 4 pur, sans Mathlib.
-/

namespace ProfRegPR16

/-! ## 1. Les trois mots de L3

> « Une condition de réfutation qui ne peut être exercée que par le
> porteur de l'inscription n'est pas une condition de réfutation. »

Trois exigences, à tenir séparées :

| | |
|---|---|
| **tiers** | quelqu'un d'autre que celui qui inscrit — l'altérité |
| **effectivement** | qui peut le faire, non qui en a le droit — les moyens |
| **exercer** | dont l'objection produit un effet — la reprise |

Un dispositif qui satisfait la première sans les deux autres —
« n'importe qui peut contester, adressez-vous au porteur » — ne
satisfait pas L3. Les trois champs ci-dessous les portent une à une,
et correspondent aux conditions 1, 3 et 4 de Longino ; la deuxième
(standards partagés, que les critiques peuvent invoquer — ici, des
règles d'inscription publiques) est portée par le palier PAL-4 lui-même et
n'a pas de champ propre. [Numérotation corrigée le 29/09/2026 — A14-a.] -/

/-- Le type des acteurs est laissé **abstrait**. C'est délibéré : le
    théorème central du §4 ne tient que si la population des tiers
    n'est pas énumérable, et cette propriété doit pouvoir être
    déclarée sur le type plutôt que supposée du modèle. -/
structure ConditionRefutation (A : Type) where
  enonce : String
  /-- Longino 1 — le lieu reconnu où la contestation se dépose.
      `none` = aucun lieu désigné. -/
  lieuDeDepot : Option String
  /-- Longino 4 — qui est admis à réfuter.
      `none` = **non restreint** ; `some l` = liste close. -/
  refutantsAdmis : Option (List A)
  /-- Longino 3 — l'objection produit un effet sur l'écriture
      (réponse de la communauté ; corrigé le 29/09/2026, était « 2 »). -/
  repriseInscrite : Bool

structure Inscription (A : Type) where
  porteurs : List A
  condition : Option (ConditionRefutation A)

/-- Qui peut effectivement exercer la condition. Une condition non
    restreinte est exerçable par tous ; une liste close ne l'est que
    par ses membres. -/
def ExercablePar {A : Type} (c : ConditionRefutation A) (a : A) : Prop :=
  match c.refutantsAdmis with
  | none => True
  | some l => a ∈ l

def Alterite {A : Type} (i : Inscription A) (c : ConditionRefutation A) : Prop :=
  ∃ a, ExercablePar c a ∧ a ∉ i.porteurs

def Moyens {A : Type} (c : ConditionRefutation A) : Prop :=
  c.lieuDeDepot ≠ none

def Reprise {A : Type} (c : ConditionRefutation A) : Prop :=
  c.repriseInscrite = true

/-- **L3.** Les trois exigences ensemble. -/
def L3 {A : Type} (i : Inscription A) (c : ConditionRefutation A) : Prop :=
  Alterite i c ∧ Moyens c ∧ Reprise c

/-- L'obligation écrite comme **condition de bonne formation** de
    l'inscription — patron de PR-3, PR-8, PR-10, PR-14 et PR-15,
    inscrit comme règle de rédaction en NT-ARCH §8octies-bis ; statut des
    dépliages fixé par NT-ARCH §8ter-bis (D-13, 28/09/2026). -/
def BienFormee {A : Type} (i : Inscription A) : Prop :=
  ∀ c, i.condition = some c → L3 i c

/-! ## 2. PR-16 -/

/-- **PR-16 — `refutation_exige_un_tiers`.** Toute inscription bien
    formée portant une condition de réfutation exhibe un réfutant
    possible qui n'est pas l'un de ses porteurs. -/
theorem refutation_exige_un_tiers {A : Type}
    (i : Inscription A) (c : ConditionRefutation A)
    (h_bf : BienFormee i) (h : i.condition = some c) :
    ∃ a, ExercablePar c a ∧ a ∉ i.porteurs :=
  (h_bf c h).1

/-- **L'auto-réfutation n'est pas une réfutation.** Une inscription
    dont les réfutants admis sont exactement ses porteurs ne peut pas
    être bien formée.

    C'est la formalisation du contre-exemple de PR-8 — « réfutable par
    le seul porteur, à huis clos » — et le cœur de L3. -/
theorem autorefutation_n_est_pas_refutation {A : Type}
    (i : Inscription A) (c : ConditionRefutation A)
    (h_bf : BienFormee i) (h : i.condition = some c)
    (h_clos : c.refutantsAdmis = some i.porteurs) : False := by
  obtain ⟨a, h_ex, h_non⟩ := (h_bf c h).1
  apply h_non
  unfold ExercablePar at h_ex
  rw [h_clos] at h_ex
  exact h_ex

/-- **Un lieu de dépôt est exigé.** Sans lieu reconnu où déposer la
    contestation, la condition n'est pas exerçable — première condition
    de Longino. -/
theorem refutation_exige_un_lieu {A : Type}
    (i : Inscription A) (c : ConditionRefutation A)
    (h_bf : BienFormee i) (h : i.condition = some c) :
    c.lieuDeDepot ≠ none :=
  (h_bf c h).2.1

/-- **La reprise est exigée.** Une objection reçue sans effet sur
    l'écriture n'est pas une réfutation — troisième condition de
    Longino, la réponse de la communauté (« responsive to such
    criticism », p. 76 ; corrigé le 29/09/2026, était « deuxième »). -/
theorem refutation_exige_une_reprise {A : Type}
    (i : Inscription A) (c : ConditionRefutation A)
    (h_bf : BienFormee i) (h : i.condition = some c) :
    c.repriseInscrite = true :=
  (h_bf c h).2.2

/-! ## 3. L'écart entre PR-8 et L3, démontré

PR-8 exige qu'une condition de réfutation soit **inscrite**. PR-16
exige qu'elle soit **exerçable**. Le théorème suivant établit que la
première n'entraîne pas la seconde — c'est-à-dire que l'arête
`PR-8 → PAL-4` du graphe était fausse et devait passer par L3. -/

theorem PR8_ne_suffit_pas :
    ∃ i : Inscription String, i.condition ≠ none ∧ ¬ BienFormee i := by
  refine ⟨{ porteurs := ["did:mrc:exploitant"]
          , condition := some { enonce := "réfutable par le seul porteur, à huis clos"
                              , lieuDeDepot := none
                              , refutantsAdmis := some ["did:mrc:exploitant"]
                              , repriseInscrite := false } }, ?_, ?_⟩
  · simp
  · intro h_bf
    exact refutation_exige_un_lieu _ _ h_bf rfl rfl

/-! ## 4. Pourquoi la liste close ne peut pas suffire — l'argument de PAL-4

C'est le pas qui fait passer de L3 au palier **PAL-4 (open source)**, et
il ne repose pas sur un principe politique mais sur une **impossibilité
d'énumération**.

Le MRC est construit sur le fait que certaines parties prenantes ne
peuvent pas participer : générations non nées, milieux, collectifs à
venir. L'ensemble des tiers susceptibles de réfuter ne peut donc pas
être arrêté au moment de l'inscription — ce tiers peut n'exister ou ne
se constituer qu'après elle.

On déclare cette propriété sur le type des acteurs, et on en tire la
conséquence. -/

/-- Une population qu'aucune liste finie n'épuise. -/
def NonEnumerable (A : Type) : Prop := ∀ l : List A, ∃ a : A, a ∉ l

/-- Lemme technique : tout élément d'une liste de naturels est majoré
    par son maximum. -/
theorem le_foldr_max : ∀ (l : List Nat) (a : Nat), a ∈ l → a ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro a h; cases h
  | cons x xs ih =>
      intro a h
      cases h with
      | head => exact Nat.le_max_left x (xs.foldr max 0)
      | tail _ h' => exact Nat.le_trans (ih a h') (Nat.le_max_right x (xs.foldr max 0))

/-- **Une population non énumérable existe** — témoin : les naturels.
    Le théorème du §4 n'est donc pas vide. -/
theorem nat_non_enumerable : NonEnumerable Nat := by
  intro l
  refine ⟨l.foldr max 0 + 1, ?_⟩
  intro h
  have hle := le_foldr_max l _ h
  omega

/-- **Toute liste close exclut quelqu'un.** Dès que la population des
    tiers n'est pas énumérable, une condition de réfutation restreinte
    à une liste laisse hors d'elle un acteur qui ne pourra jamais
    l'exercer.

    C'est l'argument de PAL-4 : le risque n'est pas qu'on ouvre trop peu,
    c'est qu'**aucune liste arrêtée aujourd'hui ne peut garantir de
    contenir le tiers qui aurait pu réfuter**.

    `[LECTURE — D-13, sous renvoi]` Dépliage de `NonEnumerable`. Témoins :
    `nat_non_enumerable` (l'hypothèse est
    satisfiable) et `PR24_l_exclusion_est_conditionnelle` (sans elle, la
    conclusion tombe). Réserve B-10 : `NonEnumerable` n'est témoigné que
    sur `Nat`. -/
theorem liste_close_exclut_toujours {A : Type}
    (h_ne : NonEnumerable A) (c : ConditionRefutation A)
    (l : List A) (h_clos : c.refutantsAdmis = some l) :
    ∃ a : A, ¬ ExercablePar c a := by
  obtain ⟨a, ha⟩ := h_ne l
  refine ⟨a, ?_⟩
  unfold ExercablePar
  rw [h_clos]
  exact ha

/-- **Et l'ouverture, elle, n'exclut personne.** Le pendant du
    théorème précédent : une condition non restreinte est exerçable
    par tout acteur, sans hypothèse sur la population.

    Les deux ensemble donnent PAL-4 : lorsque la population des tiers
    n'est pas énumérable, **seule l'ouverture garantit la
    non-exclusion**. -/
theorem ouverture_n_exclut_personne {A : Type}
    (c : ConditionRefutation A) (h : c.refutantsAdmis = none) :
    ∀ a : A, ExercablePar c a := by
  intro a
  unfold ExercablePar
  rw [h]
  trivial

/-! ## 5. Ce que PR-16 ne fait pas -/

/-- **PR-16 ne désigne aucun tiers.** Il exige qu'il puisse en exister
    un ; il ne dit ni qui, ni combien, ni comment on le qualifie.

    Ce n'est pas une omission : désigner le tiers refermerait
    l'énumération que le §4 déclare impossible. Une théorie du tiers
    légitime irait contre l'argument même de PAL-4. -/
theorem PR16_ne_designe_pas_le_tiers :
    ∃ i₁ i₂ : Inscription String,
      BienFormee i₁ ∧ BienFormee i₂ ∧
      (∃ c₁ c₂, i₁.condition = some c₁ ∧ i₂.condition = some c₂ ∧
                c₁.refutantsAdmis ≠ c₂.refutantsAdmis) := by
  refine ⟨{ porteurs := ["did:mrc:exploitant"]
          , condition := some { enonce := "contestation ouverte"
                              , lieuDeDepot := some "registre public"
                              , refutantsAdmis := none
                              , repriseInscrite := true } },
          { porteurs := ["did:mrc:exploitant"]
          , condition := some { enonce := "contestation par le collège de riverains"
                              , lieuDeDepot := some "registre public"
                              , refutantsAdmis := some ["did:mrc:riverain"]
                              , repriseInscrite := true } },
          ?_, ?_, _, _, rfl, rfl, ?_⟩
  · intro c hc
    cases hc
    exact ⟨⟨"did:mrc:quiconque", trivial, by decide⟩, by simp [Moyens], rfl⟩
  · intro c hc
    cases hc
    exact ⟨⟨"did:mrc:riverain", by simp [ExercablePar], by decide⟩, by simp [Moyens], rfl⟩
  · simp

/-- **Une inscription bien formée porte une condition de réfutation.**
    *Portée visée — déclarée, non établie par l'énoncé :* PR-16 ne garantit pas que la réfutation ait lieu. Il institue
    une possibilité ; aucun registre ne peut instituer un exercice.
    L'inscription ci-dessous est bien formée et rien dans son type
    n'enregistre qu'une objection ait jamais été déposée.

    C'est la limite de tout dispositif procédural, et Longino la porte
    aussi : l'*uptake* qu'elle exige est une propriété de la communauté
    dans le temps, pas une garantie que le registre puisse délivrer. -/
-- [B-10, 28/09/2026 — RENOMMÉ, ex-`PR16_ne_garantit_pas_l_exercice`] L'exercice n'est pas modélisé ; l'énoncé dit seulement qu'une inscription bien formée porte une condition.
theorem une_inscription_bien_formee_porte_une_condition :
    ∃ i : Inscription String, BienFormee i ∧ i.condition ≠ none := by
  refine ⟨{ porteurs := ["did:mrc:exploitant"]
          , condition := some { enonce := "contestation ouverte, jamais exercée"
                              , lieuDeDepot := some "registre public"
                              , refutantsAdmis := none
                              , repriseInscrite := true } }, ?_, ?_⟩
  · intro c hc
    cases hc
    exact ⟨⟨"did:mrc:quiconque", trivial, by decide⟩, by simp [Moyens], rfl⟩
  · simp

/-! ## Témoins D-13 (règle NT-ARCH §8ter-bis, R-2) — versés le 28/09/2026

`refutation_exige_un_tiers`, `autorefutation_n_est_pas_refutation`,
`refutation_exige_un_lieu` et `refutation_exige_une_reprise` sont des lectures
des trois clauses de L3 (R-3). `PR8_ne_suffit_pas` échoue sur les trois à la
fois : il n'est pas discriminant. Un témoin par clause ci-dessous ; témoin bien
formé : `une_inscription_bien_formee_porte_une_condition`. -/

/-- Échoue sur l'altérité seule : réfutants admis = porteurs. -/
theorem PR16_alterite_temoin_discriminant :
    ∃ (i : Inscription String) (c : ConditionRefutation String),
      i.condition = some c ∧ Moyens c ∧ Reprise c ∧ ¬ BienFormee i := by
  refine ⟨{ porteurs := ["p"], condition := some { enonce := "e", lieuDeDepot := some "l", refutantsAdmis := some ["p"], repriseInscrite := true } },
          { enonce := "e", lieuDeDepot := some "l", refutantsAdmis := some ["p"],
            repriseInscrite := true },
          rfl, (fun h => nomatch h), rfl, ?_⟩
  intro h
  obtain ⟨a, hex, hn⟩ := (h _ rfl).1
  exact hn hex

/-- Échoue sur le lieu de dépôt seul. -/
theorem PR16_moyens_temoin_discriminant :
    ∃ (i : Inscription String) (c : ConditionRefutation String),
      i.condition = some c ∧ Alterite i c ∧ Reprise c ∧ ¬ BienFormee i := by
  refine ⟨{ porteurs := [], condition := some { enonce := "e", lieuDeDepot := none, refutantsAdmis := none, repriseInscrite := true } },
          { enonce := "e", lieuDeDepot := none, refutantsAdmis := none,
            repriseInscrite := true },
          rfl, ⟨"t", trivial, List.not_mem_nil⟩, rfl, ?_⟩
  intro h
  exact (h _ rfl).2.1 rfl

/-- Échoue sur la reprise seule. -/
theorem PR16_reprise_temoin_discriminant :
    ∃ (i : Inscription String) (c : ConditionRefutation String),
      i.condition = some c ∧ Alterite i c ∧ Moyens c ∧ ¬ BienFormee i := by
  refine ⟨{ porteurs := [], condition := some { enonce := "e", lieuDeDepot := some "l", refutantsAdmis := none, repriseInscrite := false } },
          { enonce := "e", lieuDeDepot := some "l", refutantsAdmis := none,
            repriseInscrite := false },
          rfl, ⟨"t", trivial, List.not_mem_nil⟩, (fun h => nomatch h), ?_⟩
  intro h
  exact Bool.noConfusion (h _ rfl).2.2

end ProfRegPR16
