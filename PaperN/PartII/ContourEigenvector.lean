import PaperN.PartII.ResolventEigenvector

namespace PaperN.PartII
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

noncomputable def scalarSegment (a p q : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (q-p) * (segmentParameter p q t-a)⁻¹

noncomputable def scalarQuadrilateral (a p q r s : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    (scalarSegment a p q + scalarSegment a q r + scalarSegment a r s + scalarSegment a s p)

def EigenEdgeCondition (U : E →L[ℂ] E) (a p q : ℂ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter p q t ∈ resolventSet ℂ U ∧ segmentParameter p q t ≠ a

theorem quadrilateralResolvent_apply_eigenvector (U : E →L[ℂ] E) (a p q r s : ℂ)
    (hpq : EigenEdgeCondition U a p q) (hqr : EigenEdgeCondition U a q r)
    (hrs : EigenEdgeCondition U a r s) (hsp : EigenEdgeCondition U a s p)
    (v : E) (hv : U v = a • v) :
    quadrilateralResolvent U p q r s v = scalarQuadrilateral a p q r s • v := by
  have H (b c : ℂ) (hb : EigenEdgeCondition U a b c) :
      segmentResolvent U b c v = scalarSegment a b c • v :=
    segmentResolvent_apply_eigenvector U a b c (fun t ht ↦ (hb t ht).1)
      (fun t ht ↦ (hb t ht).2) v hv
  change (2 * Real.pi * Complex.I)⁻¹ •
    (segmentResolvent U p q v + segmentResolvent U q r v +
      segmentResolvent U r s v + segmentResolvent U s p v) = _
  rw [H p q hpq, H q r hqr, H r s hrs, H s p hsp]
  simp only [scalarQuadrilateral, add_smul, mul_smul, smul_add]

theorem quadrilateralResolvent_fixes_eigenvector (U : E →L[ℂ] E) (a p q r s : ℂ)
    (hpq : EigenEdgeCondition U a p q) (hqr : EigenEdgeCondition U a q r)
    (hrs : EigenEdgeCondition U a r s) (hsp : EigenEdgeCondition U a s p)
    (v : E) (hv : U v = a • v) (hc : scalarQuadrilateral a p q r s = 1) :
    quadrilateralResolvent U p q r s v = v := by
  rw [quadrilateralResolvent_apply_eigenvector U a p q r s hpq hqr hrs hsp v hv, hc, one_smul]

theorem quadrilateralResolvent_kills_eigenvector (U : E →L[ℂ] E) (a p q r s : ℂ)
    (hpq : EigenEdgeCondition U a p q) (hqr : EigenEdgeCondition U a q r)
    (hrs : EigenEdgeCondition U a r s) (hsp : EigenEdgeCondition U a s p)
    (v : E) (hv : U v = a • v) (hc : scalarQuadrilateral a p q r s = 0) :
    quadrilateralResolvent U p q r s v = 0 := by
  rw [quadrilateralResolvent_apply_eigenvector U a p q r s hpq hqr hrs hsp v hv, hc, zero_smul]
def RectangleEigenCondition (U : E →L[ℂ] E) (a : ℂ) (l r h : ℝ) : Prop :=
  EigenEdgeCondition U a ⟨l,-h⟩ ⟨r,-h⟩ ∧ EigenEdgeCondition U a ⟨r,-h⟩ ⟨r,h⟩ ∧
  EigenEdgeCondition U a ⟨r,h⟩ ⟨l,h⟩ ∧ EigenEdgeCondition U a ⟨l,h⟩ ⟨l,-h⟩

noncomputable def scalarRectangle (a : ℂ) (l r h : ℝ) : ℂ :=
  scalarQuadrilateral a ⟨l,-h⟩ ⟨r,-h⟩ ⟨r,h⟩ ⟨l,h⟩

theorem rectangleResolvent_apply_eigenvector (U : E →L[ℂ] E) (a : ℂ) (l r h : ℝ)
    (hc : RectangleEigenCondition U a l r h) (v : E) (hv : U v = a • v) :
    rectangleResolvent U l r h v = scalarRectangle a l r h • v :=
  quadrilateralResolvent_apply_eigenvector U a _ _ _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 v hv

theorem cutoffContourOperator_apply_eigenvector (U : E →L[ℂ] E) (a : ℂ) (D η : ℝ)
    (hp : RectangleEigenCondition U a η (cutoffOuter D η) 1)
    (hn : RectangleEigenCondition U a (-cutoffOuter D η) (-η) 1)
    (v : E) (hv : U v = a • v) :
    cutoffContourOperator U D η v =
      (scalarRectangle a η (cutoffOuter D η) 1 +
        scalarRectangle a (-cutoffOuter D η) (-η) 1) • v := by
  change rectangleResolvent U η (cutoffOuter D η) 1 v +
    rectangleResolvent U (-cutoffOuter D η) (-η) 1 v = _
  rw [rectangleResolvent_apply_eigenvector U a _ _ _ hp v hv,
    rectangleResolvent_apply_eigenvector U a _ _ _ hn v hv, add_smul]
end PaperN.PartII
