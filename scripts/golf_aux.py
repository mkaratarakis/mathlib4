#!/usr/bin/env python3
"""One-shot golf script for Aux.lean."""
from pathlib import Path
import re

path = Path(__file__).resolve().parents[1] / "Mathlib/LinearAlgebra/Matrix/PerronFrobenius/Aux.lean"
lines = path.read_text().splitlines(keepends=True)

out, i = [], 0
while i < len(lines):
    line = lines[i]
    if re.match(r"^/-[^!]", line):
        if "-/" in line:
            i += 1
            continue
        i += 1
        while i < len(lines) and "-/" not in lines[i]:
            i += 1
        if i < len(lines):
            i += 1
        continue
    out.append(line)
    i += 1
text = "".join(out)

if not text.startswith("/-\nCopyright"):
    text = (
        "/-\nCopyright (c) 2025 Matteo Cipollina. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: Matteo Cipollina\n"
        "-/\n" + text.lstrip()
    )

header = """open Filter Set Finset Matrix Topology Convex

/-!
# Auxiliary results for Perron–Frobenius theory

Semicontinuity on ultrafilters, matrix–vector identities, and simplex lemmas
used by `Mathlib.LinearAlgebra.Matrix.PerronFrobenius.*`.
-/

@[expose] public section

/-!
## Ultrafilters and semicontinuity
*/

"""
text = re.sub(
    r"open Filter Set Finset Matrix Topology Convex\n\n+@\[expose\] public section\n\n/-!\n## Key Theorems.*?\n-/\n\n",
    header,
    text,
    count=1,
    flags=re.DOTALL,
)
text = re.sub(r"/-!\n## Semicontinuity Theorems\n-/\n", "", text)

text = re.sub(
    r"/-!\n## Standard Simplex Properties\n-/\n\n\n-- Standard simplex.*?\n\n/-!\n## Supremum & Infimum Theorems\n-/\n\n.*?/-!\n## Filter & Ultrafilter Operations\n-/\n\n\n",
    "",
    text,
    flags=re.DOTALL,
)

eventually = """/-!
## Continuity helpers
-/

theorem eventually_to_open {α : Type*} [TopologicalSpace α] {p : α → Prop} {a : α}
    (h : ∀ᶠ x in 𝓝 a, p x) :
    ∃ U : Set α, IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, p x := by
  rcases mem_nhds_iff.mp h with ⟨U, hU_open, haU, hU⟩
  exact ⟨U, hU_open, haU, fun x hx => hU (hU_open.mem_nhds hx)⟩

"""
text = re.sub(
    r"/-!\n## Helper Lemmas for Continuity\n-/\n\n-- Eventually to open set conversion\n theorem eventually_to_open.*?\n      simp_all only\n\n",
    eventually,
    text,
    flags=re.DOTALL,
)

removals = [
    r"-- Matrix-vector multiplication component\n theorem matrix_mulVec_component.*?\n  simp \[Matrix\.mulVec\]; rfl\n\n",
    r"-- Infimum over finite type equals finset infimum\n theorem iInf_apply_eq_finset_inf'_apply_fun.*?\n  rw \[h1, h2, h3\]\n\n",
    r"-- Infimum over finite type equals conditional infimum\n theorem iInf_eq_ciInf.*?\n  simp only \[mem_univ, ciInf_unique\]\n\n",
    r"lemma isClosed_stdSimplex'.*?\n  exact IsClosed\.inter h₁ h₂\n\n",
    r"lemma bounded_stdSimplex'.*?\n  exact abs_le_of_le_of_neg_le h_le_one \(by linarith \[hv\.1 i\]\)\n\n",
    r"lemma le_div_iff.*?\n  rw \[←div_le_iff hb\]\n\n",
    r"lemma lt_not_le.*?\n  exact not_le_of_gt h_lt h_ge\n\n",
    r"section ConditionallyCompleteLinearOrder.*?end ConditionallyCompleteLinearOrder\n\n",
    r"lemma le_sSup_of_mem.*?\nle_csSup hs_bdd hy\n\n",
    r"lemma mul_vec_mul_vec.*?\n  simp \[mul_assoc\]\n\n",
    r"lemma continuousOn_iInf'.*?\n  rwa \[h_eq\]\n\n",
    r"lemma le_csSup_of_mem.*?\nle_csSup hs_bdd \(Set\.mem_image_of_mem f hy\)\n\n",
    r"lemma div_lt_iff.*?\n  lt_iff_lt_of_le_iff_le \(by exact le_div_iff₀ hc\)\n\n",
    r"lemma smul_sum.*?\n  simp only \[smul_eq_mul, Finset\.mul_sum\]\n\n",
    r"lemma ones_norm_mem_simplex.*?\n  · simp \[Finset\.sum_const, Finset\.card_univ\];\n\n",
    r"lemma Real\.le_sSup.*?\n  le_csSup h_bdd h_mem\n\n",
    r"lemma csSup_image'.*?\n  exact h₁\.unique h₂\n\n",
    r"lemma iSup_eq_sSup.*?\n  simpa using \(sSup_image' \(f := f\) \(s := s\)\)\.symm\n\n",
    r"lemma dotProduct_mulVec_assoc.*?\n  simp \[mul_comm, mul_left_comm\]\n\n",
    r"lemma transpose_mulVec.*?\n  simp \[mul_comm, mul_left_comm\]\n\n",
    r"lemma dotProduct_mulVec_comm.*?\n  rw \[dotProduct_mulVec, vecMul_eq_mulVec_transpose\]\n\n",
    r"variable \{α ι : Type\*\} \{f : ι → α\} \{s : Set ι\}\nopen Set\n-- Indexed supremum.*?\n theorem iSup_eq_sSup_image.*?\n  simp \[iSup, image_eq_range\]\n\n",
    r"lemma Finset\.iInf_apply_eq_finset_inf'_apply_fun \{α β γ.*?\n  rw \[h1, h2, h3\]\n\n",
]
for p in removals:
    text, _ = re.subn(p, "", text, flags=re.DOTALL)

iinf_lemma = """/-- `iInf` over a finite index type agrees with `Finset.inf'` on `univ`. -/
lemma Finset.iInf_apply_eq_finset_inf'_apply_fun {α β γ : Type*}
    [Fintype α] [Nonempty α] [ConditionallyCompleteLinearOrder γ]
    (f : α → β → γ) :
    (fun x ↦ ⨅ i, f i x) = (fun x ↦ (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i ↦ f i x)) := by
  ext x
  have h1 : ⨅ i, f i x = ⨅ i ∈ Set.univ, f i x := by simp only [Set.mem_univ, ciInf_unique]
  have h2 : ⨅ i ∈ Set.univ, f i x = ⨅ i ∈ (Finset.univ : Finset α), f i x := by
    congr; ext i; simp only [Set.mem_univ, ciInf_unique, mem_univ]
  have h3 : ⨅ i ∈ (Finset.univ : Finset α), f i x =
      (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i ↦ f i x) := by
    rw [Finset.inf'_eq_csInf_image]
    simp only [mem_univ, ciInf_unique, Finset.mem_univ, Finset.coe_univ, image_univ]
  rw [h1, h2, h3]

"""
if "lemma Finset.iInf_apply_eq_finset_inf'_apply_fun" not in text:
    text = text.replace(
        "/-!\n## Order & Field Properties\n-/",
        iinf_lemma + "/-!\n## Order & field properties\n-/",
    )
text = text.replace(
    "    exact iInf_apply_eq_finset_inf'_apply_fun f",
    "    exact Finset.iInf_apply_eq_finset_inf'_apply_fun f",
)
if "lemma dotProduct_mulVec_comm" not in text:
    text = text.replace(
        "lemma diagonal_mulVec_ones",
        """/-- `u ⬝ᵥ (A *ᵥ v) = (Aᵀ *ᵥ u) ⬝ᵥ v`. -/
lemma dotProduct_mulVec_comm {n : Type*} [Fintype n] (u v : n → ℝ) (A : Matrix n n ℝ) :
    u ⬝ᵥ (A *ᵥ v) = (Aᵀ *ᵥ u) ⬝ᵥ v :=
  dotProduct_mulVec u A v

lemma diagonal_mulVec_ones""",
    )

path.write_text(text)
print(f"wrote {len(text.splitlines())} lines to {path}")
