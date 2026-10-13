/-
  PR-19 · `serie_bien_formee_agregat_non_conforme`
  ================================================

  Nœud SÉR du graphe de dépendances. **Premier théorème en propre du
  palier PAL-6′** (marquage et macroéconomie) : jusqu'ici PAL-6′ n'avait que
  des patrons empruntés à V4 et à P2.

  CE QU'IL ÉTABLIT
  ----------------
  Une série d'écritures dont *chacune* satisfait la contrainte peut
  avoir un agrégat qui ne la satisfait pas. Le contrôle écriture par
  écriture — la seule forme de contrôle que le registre pratique —
  ne transfère pas à la série.

  C'est un résultat **négatif**, de la même famille que
  `registre_augmente_non_equivalence` (LotL2) et
  `PR1_ne_borne_pas_l_attribution` : il prouve un trou au lieu de le
  supposer.

  ANCRAGE
  -------
  Karl Widerquist, « How the Sufficiency Minimum Becomes a Social
  Maximum », *Utilitas*, vol. 22, n° 4, décembre 2010, p. 474-480
  (version préparatoire lue intégralement, Georgetown University SFS
  Qatar) :

    « Sufficientarian examples have been misleading because they have
      been presented IN ISOLATION. Adherents have not sufficiently
      examined the ramifications of REPEATED APPLICATION of the
      choices they ask us to make. […] A significant amount of money
      is merely the sum of many trivial amounts of money. IF WE IGNORE
      TRIVIAL LOSSES EVERY TIME WE CAUSE THEM, THEY WILL ADD UP TO
      SIGNIFICANT LOSSES. »

  Widerquist en tire que le minimum de suffisance devient un maximum
  social. Le MRC n'a pas besoin de cette conclusion normative : il a
  besoin du mécanisme, qui est un fait sur les séries.

  ⚠️ CE QUE CE FICHIER NE FAIT PAS
  --------------------------------
  Il ne transpose pas Widerquist à R-INTERDIT-ABSOLU. La question
  « la règle prescrit-elle une allocation, ou suspend-elle seulement
  une écriture ? » est posée et NON TRANCHÉE (note du 8 septembre
  2026, §1.3). Tant qu'elle l'est, PR-19 vaut pour les écritures qui
  imposent un coût, et le raccord au NiveauRIA reste
  [PLAUSIBLE, NON VÉRIFIÉ].

  Il ne dit pas non plus que le seuil est mal choisi — voir §4, où
  l'on montre qu'AUCUN seuil positif n'échappe au mécanisme.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib, sans import.
-/

namespace ProfRegPR19

/-! ## 1. Le modèle

Le modèle est délibérément pauvre : une écriture n'est rien d'autre
que le coût qu'elle impose. Toute la thèse tient dans le fait que ce
coût **s'additionne**, et rien d'autre n'est requis pour l'établir.

`[RESTE DE TRADUCTION]` Une écriture réelle porte un régime, un
porteur, un seuil, une contrepartie. Aucun de ces éléments n'entre
ici. Le théorème vaut donc de la dimension additive des écritures,
et de rien d'autre. -/

/-- Une écriture, réduite au coût entier qu'elle impose aux acteurs
    situés au-dessus du seuil. -/
structure Ecriture where
  cout : Nat

/-- L'agrégat d'une série : la somme des coûts. C'est la seule
    hypothèse de fond du fichier — que l'agrégation soit additive. -/
def agreger : List Ecriture → Nat
  | [] => 0
  | e :: r => e.cout + agreger r

/-- Conformité d'une écriture prise isolément : son coût est
    au-dessous du seuil de trivialité. -/
def trivialSous (seuil : Nat) (e : Ecriture) : Prop := e.cout ≤ seuil

/-- Conformité de la série, mesurée par le **même** seuil. C'est le
    point : on n'introduit pas un second seuil pour l'agrégat. -/
def conformeSous (seuil : Nat) (s : List Ecriture) : Prop :=
  agreger s ≤ seuil

/-! ## 2. La série de coûts triviaux -/

/-- `serieTriviale n` : `n` écritures de coût 1 chacune. -/
def serieTriviale : Nat → List Ecriture
  | 0     => []
  | n + 1 => ⟨1⟩ :: serieTriviale n

theorem agreger_serieTriviale (n : Nat) : agreger (serieTriviale n) = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [serieTriviale, agreger, ih]; omega

/-- Chaque écriture de la série est triviale, dès que le seuil est
    non nul. -/
theorem serieTriviale_est_triviale (seuil : Nat) (h : 0 < seuil) (n : Nat) :
    ∀ e ∈ serieTriviale n, trivialSous seuil e := by
  induction n with
  | zero => intro e he; cases he
  | succ k ih =>
      intro e he
      cases he with
      | head => exact h
      | tail _ hr => exact ih e hr

/-! ## 3. Le théorème -/

/-- **PR-19.** Il existe une série dont chaque écriture est conforme
    et dont l'agrégat ne l'est pas.

    La conformité écriture par écriture ne transfère pas à la série. -/
theorem serie_bien_formee_agregat_non_conforme (seuil : Nat) (h : 0 < seuil) :
    ∃ s : List Ecriture,
      (∀ e ∈ s, trivialSous seuil e) ∧ ¬ conformeSous seuil s := by
  refine ⟨serieTriviale (seuil + 1), serieTriviale_est_triviale seuil h _, ?_⟩
  simp only [conformeSous, agreger_serieTriviale]
  omega

/-! ## 4. Ce n'est pas un artefact du seuil choisi

L'objection immédiate : « votre seuil est mal placé ». Elle ne tient
pas. Le théorème du §3 est déjà universellement quantifié sur le
seuil : **aucun seuil positif n'échappe au mécanisme** — déplacer le
seuil ne fait que déplacer la longueur de la série qui le franchit
(`serie_bien_formee_agregat_non_conforme`, §3, pour tout `seuil` avec
`0 < seuil`). -/
-- [11/10/2026 — RETIRÉ, doublon d'énoncé sans usage : `aucun_seuil_positif_n_echappe`
--  (même proposition que `serie_bien_formee_agregat_non_conforme`, preuve par application directe) ;
--  nommé par aucun fichier du set MRC v5.7, cité par aucune preuve ni par `R7_Controle.lean`.]

/-! ## 5. Ce qui survit à la sommation, et c'est le résultat utile

PR-19 serait une curiosité s'il ne disait que « la somme dépasse ».
Son intérêt est de **trier** : il existe une classe de contraintes
qui, elles, passent à la série. Ce sont celles dont le seuil est nul
— c'est-à-dire les **interdictions**, par opposition aux tolérances.

C'est la contrepartie constructive : un registre qui veut contrôler
une série ne peut pas le faire avec des tolérances, seulement avec
des interdits, ou bien en inscrivant l'agrégat lui-même. -/

/-- Une écriture strictement sans coût. -/
def strictementNul (e : Ecriture) : Prop := e.cout = 0

/-- **Le seuil nul est stable par sommation.** Une série d'écritures
    strictement sans coût a un agrégat strictement sans coût. -/
theorem serie_nulle_reste_conforme :
    ∀ s : List Ecriture, (∀ e ∈ s, strictementNul e) → agreger s = 0 := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons e r ih =>
      intro h
      have he : e.cout = 0 := h e (List.Mem.head _)
      have hr : ∀ x ∈ r, strictementNul x := fun x hx => h x (List.Mem.tail _ hx)
      simp [agreger, he, ih hr]

/-- Corollaire : sous seuil nul, la conformité de chaque écriture
    entraîne la conformité de l'agrégat. **C'est exactement ce que le
    §3 nie pour tout seuil positif.** -/
theorem seuil_nul_transfere_a_la_serie (s : List Ecriture)
    (h : ∀ e ∈ s, strictementNul e) : conformeSous 0 s := by
  simp only [conformeSous, serie_nulle_reste_conforme s h]
  exact Nat.le_refl 0

/-! ## 6. Gardes

Trois énoncés qui bornent la portée de PR-19 — sans eux le théorème
serait sur-revendiqué au sens de NT-ARCH §8bis. -/

/-- PR-19 **n'interdit aucune série** : il existe des séries conformes
    à tout seuil. Le théorème porte sur l'existence d'un contre-exemple,
    non sur une propriété générale des séries. -/
theorem PR19_n_interdit_aucune_serie (seuil : Nat) :
    ∃ s : List Ecriture, s ≠ [] ∧ (∀ e ∈ s, trivialSous seuil e) ∧ conformeSous seuil s := by
  -- [B-9, 28/09/2026] Témoin refait : la série était VIDE (forme 6). Une série
  -- d'une écriture de coût égal au seuil est conforme, à tout seuil.
  refine ⟨[⟨seuil⟩], by simp, ?_, ?_⟩
  · intro e he; simp at he; subst he; exact Nat.le_refl _
  · simp [conformeSous, agreger]

/-- PR-19 **ne juge pas le seuil**. Que la série franchisse le seuil
    ne dit rien de la justesse du seuil : le §4 montre que le
    franchissement vaut pour tout seuil positif, donc qu'il ne
    discrimine aucun choix de seuil. -/
theorem PR19_ne_juge_pas_le_seuil (s₁ s₂ : Nat) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    (∃ t, (∀ e ∈ t, trivialSous s₁ e) ∧ ¬ conformeSous s₁ t)
    ∧ (∃ t, (∀ e ∈ t, trivialSous s₂ e) ∧ ¬ conformeSous s₂ t) :=
  ⟨serie_bien_formee_agregat_non_conforme s₁ h₁,
   serie_bien_formee_agregat_non_conforme s₂ h₂⟩

/-- PR-19 **ne dit rien d'une écriture isolée**. Toute écriture de coût
    au plus égal au seuil est conforme, et le reste. -/
theorem PR19_ne_touche_pas_l_ecriture_isolee (seuil : Nat) (e : Ecriture)
    (h : trivialSous seuil e) : conformeSous seuil [e] := by
  simp only [conformeSous, agreger]
  simpa [trivialSous] using h

end ProfRegPR19
