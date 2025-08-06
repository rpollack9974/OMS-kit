%attach master.sage

p = 3
M = 30

E = EllipticCurve('15a')
phiE = form_modsym_from_elliptic_curve(E)
Phi = phiE.lift_to_OMS_eigen(p,M)
R.<w> = PolynomialRing(QQ)
Phi_fam = Phi.lift_to_modsym_dist_fam(w)
Phi_fam = Phi_fam.scale(p^(-Phi_fam.valuation()))
Phi_fam = Phi_fam.hecke(p) - Phi_fam
for a in range(M+2):
	Phi_fam = Phi_fam.hecke(p)
	print(a,"out of",M+2)

## Phi_fam is now the family of Hecke-eigensymbols which specializes in weight 2 to E.

