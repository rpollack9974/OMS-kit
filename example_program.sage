load("master.sage")

p=11
E=EllipticCurve('11a')
print("Forming modular symbols (in sense of Stevens) attached to E")
phi=form_modsym_from_elliptic_curve(E)
print(phi)
print("This modular symbol is stored by its value on 3 (particular) degree zero divsiors which generator over Z[Gamma_0(11)]")
print("Lifting to an overconvergent modular symbol with 10 moments (with some Eisenstein error)")
Phi=phi.lift_to_OMS(p,10)
if Phi.valuation()<0:
	Phi=Phi.scale(p^(-Phi.valuation()))
#kills off any denominators
print(Phi)
print("An OMS of level 11 is represented by 3 distributions -- each distribution is a vector of length 10 representing the moments")
print("Apply U_p once (to deal with convergence issues) and normalizing")
Phi=Phi.hecke(p)
print(Phi)
#solving the difference equation potentially causes problems that applying Hecke once clears up (I should remind myself how this works)
print("Killing off Eisenstein part by applying T_2-3")
Phi=Phi.hecke(2)-Phi.scale(3)
#our method of lifting of classical modular symbols only works up to some Eisenstein error. 
print("Iterating U_p")
for j in range(10):
	print(j+1,"-th application of U_p")
	Phi=Phi.hecke(p); print(Phi)
#The result after applying U_p should converge to a Hecke-eigensymbol lifting a (non-zero) multiple of phi
print("Here's Phi - Phi|U_p (should be all zeroes)")
print(Phi-Phi.hecke(p))
#The result should be all zeroes -- i.e. Phi | U_p = - Phi since a_11(E)=1
print("Here's  Phi|T_19 (should be all zeroes since a_19(E)=0)")
print(Phi.hecke(19))

print("Now the 11-adic L-function of E (in terms of its moments) is given b y its value on (0) - (\infty) which is the distribution:")
print(Phi.data[0])

print("-----------------")
print("Now let's take p=3, so we need to p-stabilize to level 33")
p=3
phip=phi.p_stabilize_ordinary(3,-1,20)
print("Here's the 3-ordinary stabilization to level 33 of our original modular symbol (computed modulo 3^20).  Also, we now need 9 generators")
print(phip)
print("Now we lift as before")
Phi=phip.lift_to_OMS(p,10)
if Phi.valuation()<0:
	Phi=Phi.scale(p^(-Phi.valuation()))
#kills off any denominators
Phi=Phi.hecke(p)
Phi=Phi.hecke(2)-Phi.scale(3)
print("Iterating U_p")
for j in range(10):
	print(j+1,"-th application of U_p")
	Phi=Phi.hecke(p); print(Phi)
print("Here's 2*Phi + Phi|T_2 (should be all zeroes)")
print(Phi.scale(2)+Phi.hecke(2))
#The result should be all zeroes -- i.e. Phi | U_p = - Phi since a_2(E)=-2


