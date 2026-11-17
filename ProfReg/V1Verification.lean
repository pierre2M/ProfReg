import ProfReg.V2Verification
import Mathlib.Data.Real.Basic

-- ============================================================
-- V1  -  Commutativité du carré F4-F6
-- ============================================================

-- Score 0-5 représenté comme ℕ borné
def Score := Fin 6

-- État de l'appel immanent (F4, Jonas 1979)
structure AppelImmanent where
  score  : Score
  acteur : String          -- ← String, pas Actor

-- Puissance affirmative (F4, Morizot-Neyret 2026, Amendement A3)
structure PuissanceAffirmative where
  score         : Score
  acteur        : String   -- ← String, pas Actor
  seuilcritique : Score

-- Résultat de protection en F6
inductive ProtectionRequise where
  | absente    : ProtectionRequise
  | declenchee : String → ProtectionRequise  -- ← String, pas Actor
  deriving DecidableEq

-- ============================================================
-- LES DEUX RÈGLES DE DÉCLENCHEMENT
-- ============================================================

def R_HABITABILITE_CAPABILITE (a : AppelImmanent) : ProtectionRequise :=
  if a.score.val > 0
  then ProtectionRequise.declenchee a.acteur
  else ProtectionRequise.absente

def R_PUISSANCEAFFIRMATIVE (p : PuissanceAffirmative) : ProtectionRequise :=
  if p.score.val < p.seuilcritique.val
  then ProtectionRequise.declenchee p.acteur
  else ProtectionRequise.absente

-- ============================================================
-- HYPOTHÈSE DE COUPLAGE F4
-- ============================================================
-- [CONV-15, 28/09/2026] Ce type décrit le DOMAINE SANS MARQUEUR : les paires
-- cohérentes. Il n'interdit pas l'inscription d'une paire non cohérente ou
-- incomplète, qui s'inscrit avec le marqueur [PAIRE F4 NON COHÉRENTE] (Annexe
-- §A.15.8) ; ce marqueur se lève exactement là où les deux règles divergent
-- (`V1_commute_ssi_coherence`). A2 et A3 : amendements de NT-G2, non axiomes.

structure ActeurF4Coherent where
  acteur        : String
  appelimmanent : AppelImmanent
  puissanceaff  : PuissanceAffirmative
  meme_acteur_a : appelimmanent.acteur = acteur
  meme_acteur_p : puissanceaff.acteur = acteur
  coherence     : appelimmanent.score.val > 0 ↔
                  puissanceaff.score.val < puissanceaff.seuilcritique.val

-- ============================================================
-- THÉORÈME DE COMMUTATIVITÉ V1
-- ============================================================

theorem V1_commutatif (e : ActeurF4Coherent) :
    R_HABITABILITE_CAPABILITE e.appelimmanent =
    R_PUISSANCEAFFIRMATIVE e.puissanceaff := by
  simp only [R_HABITABILITE_CAPABILITE, R_PUISSANCEAFFIRMATIVE]
  rw [e.meme_acteur_a, e.meme_acteur_p]
  by_cases h : e.appelimmanent.score.val > 0
  · have hp := e.coherence.mp h
    simp [h, hp]
  · have hp : ¬ e.puissanceaff.score.val < e.puissanceaff.seuilcritique.val :=
        fun hc => h (e.coherence.mpr hc)
    simp [h, hp]

/-- **Caractérisation (28/09/2026).** Pour un appel immanent et une puissance
    affirmative portés par le même acteur, les deux règles de déclenchement
    rendent le même verdict **si et seulement si** la condition de cohérence
    tient. `V1_commutatif` en est le sens « si », lu dans le type
    `ActeurF4Coherent` ; ce théorème établit aussi le sens « seulement si »,
    que NT-G2 §3.2 affirmait sans appui compilé. Ce n'est pas un dépliage
    (NT-ARCH §8ter-bis, R-1) : aucune hypothèse de bonne formation. -/
theorem V1_commute_ssi_coherence (a : AppelImmanent) (p : PuissanceAffirmative)
    (h : a.acteur = p.acteur) :
    R_HABITABILITE_CAPABILITE a = R_PUISSANCEAFFIRMATIVE p ↔
      (a.score.val > 0 ↔ p.score.val < p.seuilcritique.val) := by
  unfold R_HABITABILITE_CAPABILITE R_PUISSANCEAFFIRMATIVE
  by_cases ha : a.score.val > 0 <;> by_cases hp : p.score.val < p.seuilcritique.val
  · rw [if_pos ha, if_pos hp, h]
    exact ⟨fun _ => Iff.intro (fun _ => hp) (fun _ => ha), fun _ => rfl⟩
  · rw [if_pos ha, if_neg hp]
    exact ⟨fun e => ProtectionRequise.noConfusion e, fun e => absurd (e.mp ha) hp⟩
  · rw [if_neg ha, if_pos hp]
    exact ⟨fun e => ProtectionRequise.noConfusion e, fun e => absurd (e.mpr hp) ha⟩
  · rw [if_neg ha, if_neg hp]
    exact ⟨fun _ => Iff.intro (fun x => absurd x ha) (fun x => absurd x hp), fun _ => rfl⟩

-- ============================================================
-- TÉMOINS D-13 (NT-ARCH §8ter-bis, R-2) — versés le 28/09/2026
-- ============================================================
-- `V1_commutatif` est une lecture du champ `coherence` (forme 3 logée dans
-- le type, audit B-6). Il est licite parce que la cohérence est habitée et
-- nécessaire : sans elle, les deux règles divergent pour un même acteur.

theorem V1_coherence_discrimine :
    Nonempty ActeurF4Coherent ∧
    (∃ (a : AppelImmanent) (p : PuissanceAffirmative), a.acteur = p.acteur
        ∧ R_HABITABILITE_CAPABILITE a = ProtectionRequise.declenchee a.acteur
        ∧ R_PUISSANCEAFFIRMATIVE p = ProtectionRequise.absente) :=
  ⟨⟨{ acteur := "x", appelimmanent := ⟨⟨0, by decide⟩, "x"⟩,
      puissanceaff := ⟨⟨0, by decide⟩, "x", ⟨0, by decide⟩⟩,
      meme_acteur_a := rfl, meme_acteur_p := rfl,
      coherence := ⟨fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0)⟩ }⟩,
   ⟨⟨1, by decide⟩, "x"⟩, ⟨⟨0, by decide⟩, "x", ⟨0, by decide⟩⟩, rfl, rfl, rfl⟩
