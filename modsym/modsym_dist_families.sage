class modsym_dist_fam(modsym):
	def ms(self):
		"""demotes to a regular modular symbol"""
		return modsym(self.level(),self.data,self.manin)

	def num_moments(self):
		return self.data[0].num_moments()

	def p(self):
		return self.data[0].p

	def deg(self):
		return self.data[0].deg

	## This function returns a number between 0 and p-2 which represents which 	
	## disc in weight the family is supported on -- the integer i corresponds to the
	## disc with characters with finite order part omega^i
	def disc(self):
		return self.data[0].disc()

	def change_deg(self,new_deg):
		v=[self.data[r].change_deg(new_deg) for r in range(self.ngens())]
		return modsym_dist_fam(self.level(),v,self.manin)

	def base_ring(self):
		return self.data[0].base_ring()

	def specialize(self,k):
		v=[]
		for j in range(0,len(self.data)):
			v=v+[self.data[j].specialize(k)]
		return modsym_dist_aws(self.level(),v,self.manin)
	
	def valuation(self):
		#print [self.data[j].valuation() for j in range(len(self.data))]
		return min([self.data[j].valuation() for j in range(len(self.data))])

	def normalize(self):
		v=[]
		for j in range(0,len(self.data)):
			v=v+[self.data[j].normalize()]
		return modsym_dist_fam(self.level(),v,self.manin)

	def divide(self,left):
		v=[]
		for j in range(0,len(self.data)):
			v=v+[self.data[j].divide(left)]
		return modsym_dist_fam(self.level(),v,self.manin)

	def change_precision(self,M):
		v=[]
		for j in range(0,len(self.data)):
			v=v+[self.data[j].change_precision(M)]
		return modsym_dist_fam(self.level(),v,self.manin)


	## This procedure tries to find a power series c(w) such that 
	##      self | T_q = c(w) self
	## It prints to the screen the self | T_q - c(w) self (so all displayed zeroes
	## means it worked, and it returns the power series c(w)
	def is_Tq_eigen(self,q):
		p = self.p()
		M = self.num_moments()
		R = self.data[0].moment(0).parent()
		T = PowerSeriesRing(QQ,'y',default_prec=self.deg())

		Phiq = self.hecke(q)
		aq = R(T(T(Phiq.data[0].moment(0))/T(self.data[0].moment(0))).padded_list())

		print((self.scale(aq) - Phiq).normalize())

		return ps_normalize(aq,p,M-self.valuation())

	def pLdata_has_key(self,D,a):
		return (D,a) in self._pLdata

	def add_pLdata(self,D,a,data):
		self._pLdata[(D,a)] = data

	def pLdata(self,D,a):
		return self._pLdata[(D,a)]

	## returns a boolean which indicates whether or not the family extends to the whole
	## unit disc.  in practice, this means that every coefficient of w^i is divisibly by p^i
	## (since the weight variable is normalizes as w/p)
	def extends_to_unit_disc(self):
		p = self.p()
		for i in range(self.ngens()):
			for j in range(self.num_moments()):
				v = self.data[i].moment(j)
				if not extends_to_unit_disc(v):
					return false
		return true

	def divide_by_pw(self):
		data = []
		R = self.data[0].moment(0).parent()
		w = R.gen()
		for a in range(len(self.data)):
			d = self.data[a]
			v = self.data[a].moments 
			vv = copy(v)
			for b in range(len(vv)):
				vv[b] = R(vv[b]/(p*w))
			data += [dist_fam(d.p,d.deg,d.disc(),vv,d.char())]

		ans = modsym_dist_fam(self.level(),data,self.manin)
		ans = ans.change_precision(ans.num_moments()-1)
		ans = ans.change_deg(ans.deg()-1)

		return ans		

#	@cached_function
	def phi_on_Da(self,a,D):
		"""return self_D(D_a) = self_D({infty} - {a/p}) where self_D is the quadratic twist of self;
		the value is cached in self._pLdata"""
		if self.pLdata_has_key(D,a):
			return self._pLdata[(D,a)]
		else:
			p=self.p()
			ans=self.zero_elt()
			for b in range(1,abs(D)+1):
				if gcd(b,D)==1:	
					ans=ans+self.eval(Matrix(2,2,[1,b/abs(D),0,1])*Matrix(2,2,[a,1,p,0])).act_right(Matrix(2,2,[1,b/abs(D),0,1])).scale(kronecker(D,b)).normalize()
			self.add_pLdata(D,a,ans.normalize())
			return ans.normalize()

#	@cached_function
	def basic_integral(self,a,j,D):
		"""returns ap int_{a+pZ_p} (z-{a})^j dPhi(0-infty) -- see formula [PS, sec 9.2] """
		M=self.num_moments()
		p=self.p()
#		ap=ap*kronecker(D,p)
		ans=0
		muaD = self.phi_on_Da(a,D)
		for r in range(j+1):
			ans=ans+binomial(j,r)*(a-teich(a,p,M))^(j-r)*p^r*muaD.moment(r)
		return ans

	def pLfunction_coef(self,n,r,D,gam,terms=None,error=None):
		"""Returns the n-th coefficient of the p-adic L-function in the T-variable of a quadratic twist of self.  
		If error is not specified, then the correct error bound is computed and the answer is return modulo that accuracy.

		actually answer is scaled by a_p but this only changes answer by a unit

	Inputs:
		self -- overconvergent Hecke-eigensymbol;
		n -- index of desired coefficient
		r -- twist by omega^r
		D -- discriminant of quadratic twist
		gam -- topological generator of 1+pZ_p"""

		S.<z> = PolynomialRing(QQ)
		p = self.p()
		M = self.num_moments()
#		Rpadic.<wp> = PowerSeriesRing(pAdicField(p,M))

		lb = loggam_binom(p,gam,S.0,n,2*M)

		dn = 0
		if n == 0:
			err = ceil((p-2)/(p-1) * M)
		else:
			if (error == None):
#				err = min(ceil((p-2)/(p-1) * (M-n)), min([j + lb[j].valuation(p) for j in range(M,len(lb))]))
#				err = min(ceil((p-2)/(p-1) * (M-n)), 
#					min([j + lb[j].valuation(p) for j in range(M,len(lb))])) 
				err1 = min([j + lb[j].valuation(p) for j in range(M,len(lb))])
				## this is the error from only using an approximation of the integrals
				err2 = min([ceil((p-2)/(p-1) * M) + lb[j].valuation(p) for j in range(M)])
				err = min(err1,err2)
			else:
				err = error
			lb = [lb[a] for a in range(M)]
		if terms == None:
			ran = range(len(lb)) 
		else:
			ran = range(terms)
		for j in ran:
			cjn = lb[j]
			temp = 0
			for a in range(1,p):
				temp = temp + teich(a,p,M)^(r-j)*(self.basic_integral(a,j,D))
			dn = dn + cjn*temp
		v = list(dn)
		v = [v[a] + O(p^err) for a in range(len(v))]
		t = 0*w
		for j in range(len(v)):
			t += v[j] * w^j
		dn = t
		return dn


	def pLfunction(self,r=0,mx=Infinity,quad_twist=None,verbose=false):
		"""Returns the p-adic L-function in the T-variable of a quadratic twist of self

	actually answer is scaled by a_p but this only changes answer by a unit
	
	Inputs:
		self -- overconvergent Hecke-eigensymbol;
		r -- twist by omega^r
		quad_twist -- conductor of quadratic character"""

		if quad_twist==None:
			D=1
		else:
			D=quad_twist
		M=self.num_moments()
		p=self.p()
		gam=1+p

		SS.<T> = PolynomialRing(self.base_ring())
		ans = self.pLfunction_coef(0,r,D,gam)+0*T
		S.<z>=PolynomialRing(QQ)
		err=Infinity
		n=1
		while (err>0) and (n<min(M,mx)):
			if verbose:
				print("working on coefficient:",n)
			lb=loggam_binom(p,gam,z,n,2*M)
			es = []
			for f in range(M):
				e1 = min([j + lb[j].valuation(p) for j in range(f+1,len(lb))])
				e2 = min([ceil((p-2)/(p-1) * M) + lb[j].valuation(p) for j in range(f+1)])
				es += [min(e1,e2)]
			err = max(es)
			terms = es.index(err) + 1
#			err1 = min([j + lb[j].valuation(p) for j in range(M,len(lb))])
#			print("n=",n)
#			print("err1",[j + lb[j].valuation(p) for j in range(0,len(lb))])
#			## this is the error from only using an approximation of the integrals
#			err2 = min([ceil((p-2)/(p-1) * M) + lb[j].valuation(p) for j in range(M)])
#			print("err2",[ceil((p-2)/(p-1) * M) + lb[j].valuation(p) for j in range(M)])

#			err = min(err1,err2)
#			if verbose:
#				print("errors",n,err,err1,err2)
#			err=min([j+lb[j].valuation(p) for j in range(M,len(lb))])
			if err>0:
				dn=self.pLfunction_coef(n,r,D,gam,error=err,terms=terms)
				ans=ans+dn*T^n

			n = n + 1

		return ans


	
#######################################################################################################################
##  This function produces a random family of OMSs.
##
##  p -- prime
##  N -- tame level
##  char -- character of conductor dividing N (or maybe Np?)
##  M -- number of moments
##  r -- integer between 0 and p-2 indicating which disc on weight space we are working
##  w -- variable which is just carried around because I had trouble with symbols being defined over different rings
#####################################################################################################################
def random_OMS_fam(p,N,char,M,r,w):
	deg = M
	v = []

	manin = manin_relations(N*p)

	## this loop runs through each generator (different from D_infty) and picks a random value for that generator
	for j in range(1,len(manin.gens)):
		rj = manin.gens[j]
		mus = random_dist_fam(p,M,deg,r,char,w)
		if (manin.twotor.count(rj) == 0) and (manin.threetor.count(rj) == 0):
			v = v + [mus]
		elif (manin.twotor.count(rj) != 0):
			## Case of two torsion (See [PS] section 4.1)
			gam = manin.gen_rel_mat(j)
			v = v + [(mus - mus.act_right(gam)).scale(1/2)]
		else:
			## Case of three torsion (See [PS] section 4.1)	
			gam = manin.gen_rel_mat(j)
			v = v + [(mus.scale(2) - mus.act_right(gam) - mus.act_right(gam^2)).scale(1/3)]

	t = v[0].zero()
	## This loops adds up around the boundary of fundamental domain except the two verticle lines
	for j in range(1,len(manin.gens)):
		rj = manin.gens[j]
		if (manin.twotor.count(rj) == 0) and (manin.threetor.count(rj) == 0):
			t = t + v[j-1].act_right(manin.gen_rel_mat(j)) - v[j-1]
		else:
			t = t - v[j-1]


	## t now should be sum Phi(D_i) | (gamma_i - 1) - sum Phi(D'_i) - sum Phi(D''_i)
	## (Here I'm using the opposite sign convention of [PS1] regarding D'_i and D''_i)

	## We now need to make some adjustment of Phi(D_i) to make t have total measure 0

	j = 1
	rj = manin.gens[j]
	gam = manin.gen_rel_mat(j)
	while (j < len(manin.gens)-1) and ((manin.twotor.count(rj) != 0) or (manin.threetor.count(rj) != 0) or (r!=0 and gam[0,0]^r%p==1)):
		j = j + 1
		rj = manin.gens[j]
		gam = manin.gen_rel_mat(j)
	assert j < len(manin.gens) - 1, "Everything is 2 or 3 torsion!  NOT YET IMPLEMENTED IN THIS CASE"

	gam = manin.gen_rel_mat(j)
	a = gam[0,0]
	c = gam[1,0]
	K = aut(p,deg,M,a,c,r,char,w)
	K0 = K[0]  ## K0 is the coefficient of z^0 in K
	K1 = K[1]  ## K1 is the coefficient of z^1 in K
	t0 = t.moment(0)
	T = PowerSeriesRing(QQ,'ww',default_prec=deg)
	err = mus.zero()

	k = r
	if r != 0:
		## The following code simply computes -t0/(K0-1)
		temp = T(T(-t0)/T(K[0]-1))
		temp = temp.truncate(deg)
		R = w.parent()
		temp = R(temp.padded_list())

		print("The result will be a lifting modulo p^",valuation(temp.substitute(w=((1+p)^k-1)/p),p))
		err.moments[0] = temp
	else:
		## The following code simply computes -t0/(K1)
		temp=T(T(-t0)/T(K1))
		temp=temp.truncate(deg)
		R = w.parent()
		temp=R(temp.padded_list())
		print("The result will be a lifting modulo p^",valuation(temp.substitute(w=((1+p)^k-1)/p),p))
		err.moments[1] = temp

	v[j-1] = v[j-1] + err
	t = t + err.act_right(gam)-err
	print("Checking that t has total measure 0: ",t.normalize().moment(0))

	mus = t.solve_diff_eqn()
	print((mus.act_right(Matrix(2,2,[1,1,0,1]))-mus-t).normalize())

	v = [mus.scale(-1)] + v

	Phis = modsym_dist_fam(N*p,v,manin)

	return Phis


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
	logpgam=L.substitute(gam-1)
	loggam=L/logpgam
#	print loggam
#	print binomial(loggam,n)

	return binomial(loggam,n).list()

def extends_to_unit_disc(P):
	v = P.padded_list()
	for a in range(len(v)):
		if v[a] != 0 and v[a] % p^a != 0:
			print("Fails at coefficient w^",a)
			print(a,v[a],v[a]%p^a)
			return false
	return true

def extends_to_unit_disc_two_variable(P):
	v = P.padded_list()
	for a in range(len(v)):
		if not extends_to_unit_disc(v[a]):
			print("Fails at coefficient T^",a)
			return false
	return true

def temp(Phi,n,r,D,gam,error=None):
	"""Returns the n-th coefficient of the p-adic L-function in the T-variable of a quadratic twist of self.  
	If error is not specified, then the correct error bound is computed and the answer is return modulo that accuracy.

	actually answer is scaled by a_p but this only changes answer by a unit

Inputs:
	self -- overconvergent Hecke-eigensymbol;
	n -- index of desired coefficient
	r -- twist by omega^r
	D -- discriminant of quadratic twist
	gam -- topological generator of 1+pZ_p"""

	S.<z> = PolynomialRing(QQ)
	p = Phi.p()
	M = Phi.num_moments()
#		Rpadic.<wp> = PowerSeriesRing(pAdicField(p,M))

	lb = loggam_binom(p,gam,S.0,n,2*M)

	dn = 0
	if n == 0:
		err = ceil((p-2)/(p-1) * M)
	else:
		if (error == None):
#				err = min(ceil((p-2)/(p-1) * (M-n)), min([j + lb[j].valuation(p) for j in range(M,len(lb))]))
			## this is the error from truncating the tail
			err1 = min([j + lb[j].valuation(p) for j in range(M,len(lb))])
			## this is the error from only using an approximation of the integrals
			err2 = min([ceil((p-2)/(p-1) * M) + lb[j].valuation(p) for j in range(M)])
			err = min(err1,err2)
			print("errors",err,err1,err2)
#			err = min(ceil((p-2)/(p-1) * (M-n)), 
#				min([j + lb[j].valuation(p) for j in range(M,len(lb))])) 
		else:
			err = error
		lb = [lb[a] for a in range(M)]
	for j in range(len(lb)):
		cjn = lb[j]
		temp = 0
		for a in range(1,p):
			temp = temp + teich(a,p,M)^(r-j)*(Phi.basic_integral(a,j,D))
		dn = dn + cjn*temp
	v = list(dn)
	v = [v[a] + O(p^err) for a in range(len(v))]
	t = 0*w
	for j in range(len(v)):
		t += v[j] * w^j
	dn = t
	return dn


def errors(p,M):
	"""Returns the p-adic L-function in the T-variable of a quadratic twist of self

actually answer is scaled by a_p but this only changes answer by a unit

Inputs:
	self -- overconvergent Hecke-eigensymbol;
	r -- twist by omega^r
	quad_twist -- conductor of quadratic character"""

	gam=1+p

	S.<z>=PolynomialRing(QQ)
	for n in range(1,M):
		lb=loggam_binom(p,gam,z,n,2*M)
		es = []
		for f in range(M):
			e1 = min([j + lb[j].valuation(p) for j in range(f+1,len(lb))])
			e2 = min([ceil((p-2)/(p-1) * M) + lb[j].valuation(p) for j in range(f+1)])
			es += [min(e1,e2)]
		err = max(es)
		terms = es.index(err) + 1
		print("n=",n,"error=",err,"terms=",terms)
	return ans

