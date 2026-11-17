/-
  PR-9 · `canal_EA`
  =================

  Annexe §C-II.2 : *« Existence et cohérence du canal E→A
  (G-EVOLUTIVITE → G-AFFECTIF) **sans cycle**. »* NT-G1 ↔ NT-G9.

  LE NŒUD ÉTAIT DÉCLARÉ BLOQUÉ, ET IL NE L'EST QU'À MOITIÉ
  --------------------------------------------------------
  Le set conditionne PR-9 à l'instrumentation `signalversaffectif` en
  F5, non faite (Vague B.3, `[INCOHÉRENCE INTER-COUCHES résiduelle]`,
  NT-ARCH §F5.4). **Ce qui est bloqué est le contenu du canal ; sa
  forme ne l'est pas.** Appliquant l'enseignement de PR-11, le canal
  entre ici comme **paramètre**.

  ET L'ÉNONCÉ DU SET EST INEXACT — C'EST LE RÉSULTAT PRINCIPAL
  -------------------------------------------------------------
  Le set décrit **les deux sens** :
  · E→A : « modificateur_affectif reçoit de G-AFFECTIF, modifie
    seuildisposition » (NT-G1 §4.3) ;
  · A→E : « résistance_cognitive_révision = FORTE peut expliquer
    idéologie_défensive_détectée persistante » (NT-G9).

  **Deux sens entre deux grammaires forment un cycle.** « Sans cycle »
  est donc faux au niveau du graphe, et §2 le démontre. Ce qui peut
  être exigé à la place — et qui est ce que « cohérence » voulait
  dire — est la **terminaison** : la propagation composée atteint un
  point fixe au lieu de se relancer indéfiniment. §3 l'énonce, §4
  montre qu'elle n'est pas gratuite.

  `[RÉSERVE DE MODÈLE]` `EtatEA`, `canalEA` et `canalAE` sont mes
  structures ; le canal E→A y est **un paramètre**, précisément parce
  que le set ne l'a pas instrumenté.

  `[CORRESPONDANCE DES ÉTIQUETTES — 12/10/2026]` Les noms de ce fichier
  ne suivent pas ceux de NT-G9 §10.2 et de NT-ARCH F5. Ici, `canalEA`
  écrit `seuilDisposition` à partir du modificateur affectif : c'est le
  sens que NT-G9 appelle **A→E** (G-AFFECTIF → G-EVOLUTIVITE). `canalAE`
  propage le modificateur vers la résistance ; le sens que NT-G9 appelle
  **E→A** (résistance FORTE → idéologie défensive) est instrumenté en F5
  par `signalversaffectif`. Les résultats (cycle, ordres différents,
  terminaison) ne dépendent que de ce que chaque sens lit ce que l'autre
  écrit. Les identifiants sont conservés : ils sont cités par le set
  (Consolidé, table R-7) et par `R7_Controle.lean`.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib, sans import.
-/

namespace ProfRegPR9

/-! ## 1. Le modèle, et le canal non instrumenté est un paramètre -/

/-- L'état couplé des deux grammaires, réduit aux deux champs que le
    set nomme dans le couplage. -/
structure EtatEA where
  /-- G-EVOLUTIVITE : `resistance_cognitive_revision` forte ? -/
  resistanceForte : Bool
  /-- G-AFFECTIF : `modificateur_affectif`. -/
  modificateurAffectif : Bool
  /-- G-EVOLUTIVITE : `seuildisposition`, que E→A modifie. -/
  seuilDisposition : Nat
  deriving DecidableEq, Repr

/-- **Le canal E→A, non instrumenté — donc paramétré.** Une fonction
    de l'état vers le nouveau `seuilDisposition`. Rien ici ne suppose ce
    qu'elle calcule ; c'est exactement ce que la Vague B.3 doit fixer. -/
structure CanalEA where
  nouveauSeuil : EtatEA → Nat

/-- Le sens A→E, lui, est décrit par le set : une résistance forte
    explique une idéologie défensive persistante — modélisée ici comme
    la propagation du modificateur affectif vers la résistance. -/
def canalAE (e : EtatEA) : EtatEA :=
  { e with resistanceForte := e.resistanceForte || e.modificateurAffectif }

def canalEA (c : CanalEA) (e : EtatEA) : EtatEA :=
  { e with seuilDisposition := c.nouveauSeuil e }

/-! ## 2. « Sans cycle » est faux, et il faut le dire

Le résultat principal du fichier, et il porte contre l'énoncé du set. -/

/-- **PR-9 (1).** Les deux canaux existent et se composent dans les deux
    ordres : `E→A→E` et `A→E→A` sont l'un et l'autre définis. **Le
    couplage G-EVOLUTIVITE ↔ G-AFFECTIF est donc un cycle du graphe des
    grammaires.**

    On l'écrit sans détour parce que c'est ce que l'énoncé « sans
    cycle » de §C-II.2 nie. -/
-- [B-10, 28/09/2026 — NOM À LIRE] Forme 1 : vrai de toutes fonctions composables (audit B-1). La réfutation de « sans cycle » est portée par `les_deux_ordres_different`, non par celui-ci.
theorem le_couplage_est_un_cycle (c : CanalEA) (e : EtatEA) :
    ∃ e₁ e₂ : EtatEA,
      canalEA c (canalAE e) = e₁ ∧ canalAE (canalEA c e) = e₂ :=
  ⟨canalEA c (canalAE e), canalAE (canalEA c e), rfl, rfl⟩

/-- **Et les deux ordres ne donnent pas le même état.** Il existe un
    canal E→A et un état sur lesquels `E→A` puis `A→E` diffère de
    `A→E` puis `E→A`. **Le carré ne commute pas** — même figure que
    VJE, et pour la même raison : l'un des deux sens lit ce que l'autre
    vient d'écrire. -/
theorem les_deux_ordres_different :
    ∃ (c : CanalEA) (e : EtatEA),
      canalEA c (canalAE e) ≠ canalAE (canalEA c e) := by
  refine ⟨⟨fun s => if s.resistanceForte then 1 else 0⟩,
          ⟨false, true, 0⟩, ?_⟩
  intro h
  have : (canalEA ⟨fun s => if s.resistanceForte then 1 else 0⟩
            (canalAE ⟨false, true, 0⟩)).seuilDisposition
       = (canalAE (canalEA ⟨fun s => if s.resistanceForte then 1 else 0⟩
            ⟨false, true, 0⟩)).seuilDisposition := congrArg EtatEA.seuilDisposition h
  simp [canalEA, canalAE] at this

/-! ## 3. Ce qui peut être exigé à la place : la terminaison

C'est ce que « cohérence » voulait dire, et c'est formulable sans
instrumenter le canal. -/

/-- **La condition de terminaison.** Un canal E→A **termine** si un
    second passage ne change plus rien : la propagation atteint un point
    fixe. C'est la contrainte que « sans cycle » cherchait, et elle
    porte sur le canal, non sur le graphe. -/
def Termine (c : CanalEA) : Prop :=
  ∀ e : EtatEA, canalEA c (canalEA c e) = canalEA c e

/-- **PR-9 (2).** La terminaison n'est pas vide : un canal qui ne lit
    pas le seuil qu'il écrit termine. C'est le cas décrit par le set —
    `modificateur_affectif` **reçoit de G-AFFECTIF** et modifie
    `seuildisposition` : le seuil n'entre pas dans son propre calcul. -/
theorem un_canal_qui_ne_relit_pas_le_seuil_termine
    (f : Bool → Bool → Nat) :
    Termine ⟨fun s => f s.resistanceForte s.modificateurAffectif⟩ := by
  intro e
  rfl

/-- **PR-9 (3).** Et elle n'est pas gratuite : il existe un canal qui
    **ne termine pas**, parce qu'il relit le seuil qu'il vient
    d'écrire. La condition trie donc, et son inscription a un contenu. -/
theorem un_canal_qui_relit_le_seuil_ne_termine_pas :
    ¬ Termine ⟨fun s => s.seuilDisposition + 1⟩ := by
  intro h
  have := h ⟨false, false, 0⟩
  have h2 : (canalEA ⟨fun s => s.seuilDisposition + 1⟩
              (canalEA ⟨fun s => s.seuilDisposition + 1⟩ ⟨false, false, 0⟩)).seuilDisposition
          = (canalEA ⟨fun s => s.seuilDisposition + 1⟩ ⟨false, false, 0⟩).seuilDisposition :=
    congrArg EtatEA.seuilDisposition this
  simp [canalEA] at h2

/-- **PR-9 (4) — la condition, sous la forme d'une obligation.** Un
    canal E→A est **bien formé** s'il termine. C'est ce que la Vague B.3
    devra vérifier au moment d'instrumenter `signalversaffectif`, et
    c'est vérifiable sur le canal seul, sans connaître G-AFFECTIF. -/
theorem la_terminaison_se_verifie_sur_le_canal_seul (c : CanalEA)
    (h : ∀ e : EtatEA, c.nouveauSeuil { e with seuilDisposition := c.nouveauSeuil e }
                         = c.nouveauSeuil e) :
    Termine c := by
  intro e
  unfold canalEA
  simp only []
  exact congrArg (fun n => { e with seuilDisposition := n }) (h e)

/-! ## 4. Gardes -/

/-- **PR-9 n'instrumente pas le canal.** Le paramètre reste libre : deux
    canaux différents donnent deux propagations différentes, et le
    fichier n'en préfère aucun. C'est la Vague B.3 qui doit choisir. -/
theorem PR9_n_instrumente_pas_le_canal :
    ∃ c₁ c₂ : CanalEA, ∃ e : EtatEA, canalEA c₁ e ≠ canalEA c₂ e := by
  refine ⟨⟨fun _ => 0⟩, ⟨fun _ => 1⟩, ⟨false, false, 0⟩, ?_⟩
  intro h
  have := congrArg EtatEA.seuilDisposition h
  simp [canalEA] at this

/-- **PR-9 ne supprime pas le cycle, il le rend inoffensif.** Le
    couplage reste bidirectionnel — c'est ce que le set décrit — et la
    terminaison ne l'interdit pas : elle borne la propagation. Sans
    cette garde, PR-9 se lirait comme une suppression du canal A→E. -/
theorem PR9_ne_supprime_pas_le_canal_AE (e : EtatEA)
    (h : e.modificateurAffectif = true) :
    (canalAE e).resistanceForte = true := by
  unfold canalAE
  simp only []
  rw [h]
  simp

/-- **PR-9 ne dit rien de la justesse du seuil.** Deux canaux qui
    terminent l'un et l'autre peuvent écrire des seuils différents : la
    terminaison est une propriété de forme, jamais de contenu. -/
theorem PR9_ne_juge_pas_le_seuil :
    Termine ⟨fun _ => 0⟩ ∧ Termine ⟨fun _ => 7⟩ :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- **Témoin discriminant** (R-7, 28/09/2026) de la lecture
    `PR9_ne_supprime_pas_le_canal_AE` : sans modificateur affectif ni
    résistance préalable, `canalAE` rend l'**autre** valeur (`false`).
    Relevé manquant à la relecture des 45 universels à preuve longue. -/
theorem PR9_canalAE_temoin_discriminant :
    (canalAE ⟨false, false, 0⟩).resistanceForte = false := rfl

end ProfRegPR9
