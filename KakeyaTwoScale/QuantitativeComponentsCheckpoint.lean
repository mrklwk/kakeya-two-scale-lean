module
public import KakeyaTwoScale.ActualArchiveMassToLength
public import KakeyaTwoScale.BilinearCylinderInput
public import KakeyaTwoScale.FiniteWedgeBands
public import KakeyaTwoScale.TinyWedgeCylinderEstimate
public import KakeyaTwoScale.WeightedArchiveMass
public import KakeyaTwoScale.KakeyaPublished

@[expose] public section

/-! Verified quantitative components, not a proof of the remaining published
multilinear contract. In particular, archive normalization retains its actual
tuple-density factor and the analytic input proved here is bilinear. -/

#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_archive_mass_to_length
#print axioms KakeyaTwoScale.flatCylinder_bilinear_integral
#print axioms KakeyaTwoScale.tiny_wedge_cylinder_estimate
#print axioms KakeyaTwoScale.original_wedge_dyadic_rpow_le
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshot_weighted_mass
#print KakeyaTwoScale.kakeya_upperMinkowski_lower_of_published_zahl
