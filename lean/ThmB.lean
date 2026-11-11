import GeneralPieces.Main

/-- Theorem B of the 3-SAT paper (Appendix B), pure form: pieces with parameters (1/√2, c). -/
theorem thmB : AppHalfPieces.ThmHalfPiecesPure :=
  GeneralPieces.thmHalfPiecesPure AppHalfPieces.pieceFacts

#print axioms thmB
