@cached_function
def teich(a,p,M):
	R=pAdicField(p,M)
	return ZZ(R.teichmuller(a))

#@cached_function
def logp(p,z,M):
	"""returns the truncation sum_{j=1}^{M-1} (-1)^(j+1)/j z^j of log_p(1+z)"""
	ans=0
	for j in range(1,M):
		ans=ans+(-1)^(j+1)/j*z^j
	return ans

@cached_function
def loggam_binom(p,gam,z,n,M):
	L=logp(p,z,M)
	logpgam=L.substitute(z=(gam-1))
	loggam=L/logpgam
#	print loggam
#	print binomial(loggam,n)

	return binomial(loggam,n).list()
	
#@cached_function
def phi_on_Da(Phi,a,D):
	p=Phi.p()
	ans=Phi.zero_elt()
	for b in range(1,abs(D)+1):
		if gcd(b,D)==1:	
			ans=ans+Phi.eval(Matrix(2,2,[1,b/abs(D),0,1])*Matrix(2,2,[a,1,p,0])).act_right(Matrix(2,2,[1,b/abs(D),0,1])).scale(kronecker(D,b)).normalize()
	return ans.normalize()

#@cached_function
def basic_integral(Phi,a,j,ap,D):
	"""returns int_{a+pZ_p} (z-{a})^j dPhi(0-infty) -- see formula [PS, sec 9.2] """
	M=Phi.num_moments()
	p=Phi.p()
	ap=ap*kronecker(D,p)
	ans=0
	phiDa = phi_on_Da(Phi,a,D)
	for r in range(j+1):
		ans=ans+binomial(j,r)*(a-teich(a,p,M))^(j-r)*p^r*phiDa.moment(r)
	return ans/ap

def pLfunction_coef(Phi,ap,n,r,D,gam,base_ring=QQ,error=None):
	"""Returns the n-th coefficient of the p-adic L-function in the T-variable of a quadratic twist of Phi.  If error is not specified, then the correct error bound is computed and the answer is return modulo that accuracy.

Inputs:
	Phi -- overconvergent Hecke-eigensymbol;
	ap -- eigenvalue of U_p;
	n -- index of desired coefficient
	r -- twist by omega^r
	D -- discriminant of quadratic twist
	gam -- topological generator of 1+pZ_p"""


	S.<z>=PolynomialRing(QQ)
	p=Phi.p()
	M=Phi.num_moments()
	R=pAdicField(p,M)
	lb=loggam_binom(p,gam,S.0,n,2*M)
	dn=0
	if n==0:
		err=M
	else:
		if (error==None):
			err=min([j+lb[j].valuation(p) for j in range(M,len(lb))])
		else:
			err=error
		lb=[lb[a] for a in range(M)]
	for j in range(len(lb)):
		cjn=lb[j]
		temp=0
		for a in range(1,p):
#			print(j,a,len(lb))
			temp=temp+teich(a,p,M)^(r-j)*basic_integral(Phi,a,j,ap,D)
		dn=dn+cjn*temp
	if base_ring == QQ:
		return dn+O(p^err)
	else:
		v = list(dn)
		v = [v[a] + O(p^err) for a in range(len(v))]
		t = 0*w
		for j in range(len(v)):
			t += v[j] * w^j
		dn = t
		return dn


def pLfunction(Phi,ap,r=0,max=Infinity,base_ring=QQ,quad_twist=None):
	"""Returns the p-adic L-function in the T-variable of a quadratic twist of Phi

Inputs:
	Phi -- overconvergent Hecke-eigensymbol;
	ap -- eigenvalue at p;
	r -- twist by omega^r
	quad_twist -- conductor of quadratic character"""

	if quad_twist==None:
		D=1
	else:
		D=quad_twist
	M=Phi.num_moments()
	p=Phi.p()
	gam=1+p
#	for a in range(1,p):
#		for j in range(M):
#			basic_integral(Phi,a,j,ap,D)

	SS.<T>=PowerSeriesRing(base_ring,default_prec=M)
	ans=pLfunction_coef(Phi,ap,0,r,D,gam,base_ring=base_ring)+0*T
	S.<z>=PolynomialRing(QQ)
	err=Infinity
	n=1
	while (err>0) and (n<min(M,max)):
		lb=loggam_binom(p,gam,z,n,2*M)
		err=min([j+lb[j].valuation(p) for j in range(M,len(lb))])
		if err>0:
			dn=pLfunction_coef(Phi,ap,n,r,D,gam,base_ring=base_ring,error=err)
			ans=ans+dn*T^n

		n=n+1

	return ans

def lambda_inv(L,p,verbose=false):
	if L==0:
		return infinity
	else:
		v=L.list()
		vals=[v[a].valuation(p) for a in range(len(v))]
		if verbose:
			print(vals)
		return vals.index(min(vals))

def mu_inv(L,p,verbose=false):
	if L==0:
		return infinity
	else:
		v=L.list()
		vals=[v[a].valuation(p) for a in range(len(v))]
		if verbose:
			print(vals)
		return min(vals)
