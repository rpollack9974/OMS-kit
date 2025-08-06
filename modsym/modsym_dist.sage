class modsym_dist(modsym):
	def ms(self):
		"""demotes to a regular modular symbol"""
		return modsym(self.level(),self.data,self.manin)

	def p(self):
		"""returns the underlying prime"""
		return self.data[0].p

	def weight(self):
		"""returns the underlying weight"""		
		return self.data[0].weight

	def num_moments(self):
		"""returns the number of moments of each value of self"""
		return self.data[0].num_moments()

	def eval(self,A):
		"""here A is a 2x2 matrix and this function returns self evaluated and the divisor attached to A = A(\infty)-A(0)"""
		ans=self.ms().eval(A)
		return ans.normalize()

	def specialize(self):
		"""returns the underlying classical symbol of weight k -- i.e. apfies the canonical map D_k --> Sym^k to all values of self"""
		v=[]
		for j in range(0,len(self.data)):
			v=v+[self.data[j].specialize()]
		return modsym_symk(self.level(),v,self.manin)
	
	def valuation(self):
		"""returns the exponent of the highest power of p which divides all moments of all values of self"""
		return min([self.data[j].valuation() for j in range(0,len(self.data))])

	def normalize(self):
		"""normalized every values of self -- e.g. reduces each values j-th moment modulo p^(N-j)"""
		if self.valuation()>=0:
			v=[]
			for j in range(0,len(self.data)):
				v=v+[self.data[j].normalize()]
			ans=modsym_dist(self.level(),v,self.manin,self.full_data)
			ans.normalize_full_data()
			
			return ans
		else:
			return self

	def normalize_aws(self):
		"""normalized every values of self -- e.g. reduces each values j-th moment modulo p^ceil((N-j)*(p-2)/(p-1)"""
		assert self.valuation()>=0, "moments are not integral"
		v=[]
		for j in range(0,len(self.data)):
			v=v+[self.data[j].aws_normalize()]
		ans=modsym_dist(self.level(),v,self.manin,self.full_data)
		ans.normalize_full_data()
		
		return ans

	def change_precision(self,M):
		"""only holds on to M moments of each value of self"""
		v=[]
		for j in range(0,len(self.data)):
			v=v+[self.data[j].change_precision(M)]
		return modsym_dist(self.level(),v,self.manin)

	def lift(self,phi,ap):
		"""Greenberg trick of lifting and applying U_p --- phi is the (exact) classical symbol"""
		v=[]
		for a in range(self.ngens()):
			v=v+[self.data[a].lift()]
		Phi=modsym_dist(self.level(),v,self.manin)
		k=self.weight()
		for a in range(self.ngens()):
			for j in range(k+1):
				Phi.data[a].moments[j]=(phi.data[a].coef(j))%(p^(Phi.num_moments()))
		return Phi.hecke(self.p()).scale(1/ap).normalize()


	##  This function forms a family of OMSs which specialize to the given OMS
	def lift_to_modsym_dist_fam(self,w):
		p = self.p()
		M = self.num_moments()
		k = self.weight()
		r = self.weight() % (p-1)
		chi = self.data[0].char()
		deg = ceil(M*(p-2)/(p-1))
		v = []

		## this loop runs through each generator and lifts the value of self on that generator to D
		for j in range(1,len(self.manin.gens)):
			rj = self.manin.gens[j]
			if (self.manin.twotor.count(rj) == 0) and (self.manin.threetor.count(rj) == 0):
				v = v + [self.data[j].lift_to_dist_fam(deg,r,w)]
			elif (self.manin.twotor.count(rj) != 0):
				## Case of two torsion (See [PS] section 4.1)
				gam = self.manin.gen_rel_mat(j)
				mu = self.data[j].lift_to_dist_fam(deg,r,w)
				v = v + [(mu - mu.act_right(gam)).scale(1/2)]
			else:
				## Case of three torsion (See [PS] section 4.1)	
				gam = self.manin.gen_rel_mat(j)
				mu = self.data[j].lift_to_dist_fam(deg,r,w)
				v = v + [(mu.scale(2) - mu.act_right(gam) - mu.act_right(gam^2)).scale(1/3)]

		t = v[0].zero()
		## This loops adds up around the boundary of fundamental domain except the two verticle lines
		for j in range(1,len(self.manin.gens)):
			rj = self.manin.gens[j]
			if (self.manin.twotor.count(rj) == 0) and (self.manin.threetor.count(rj) == 0):
				t = t + v[j-1].act_right(self.manin.gen_rel_mat(j)) - v[j-1]
			else:
				t = t - v[j-1]


		## t now should be sum Phi(D_i) | (gamma_i - 1) - sum Phi(D'_i) - sum Phi(D''_i)
		## (Here I'm using the opposite sign convention of [PS1] regarding D'_i and D''_i)

		## We now need to make some adjustment of Phi(D_i) to make t have total measure 0

		j = 1
		rj = self.manin.gens[j]
		gam = self.manin.gen_rel_mat(j)
		a = gam[0,0]
		c = gam[1,0]

		while (j < len(self.manin.gens)-1) and ((self.manin.twotor.count(rj) != 0) or (self.manin.threetor.count(rj) != 0) or (r == 0 and c == 0) or (r != 0 and (chi(a)*(a^r))%p == 1)):
			j = j + 1
			rj = self.manin.gens[j]
			gam = self.manin.gen_rel_mat(j)
			a = gam[0,0]
			c = gam[1,0]

		assert j < len(self.manin.gens) - 1, "Everything is 2 or 3 torsion -- or other problems!  NOT YET IMPLEMENTED IN THIS CASE"

		gam = self.manin.gen_rel_mat(j)

		a = gam[0,0]
		c = gam[1,0]
		chi = self.data[0].char()
		K = aut(p,deg,M,a,c,r,chi,w)
		K0 = K[0]  ## K0 is the coefficient of z^0 in K
		K1 = K[1]  ## K1 is the coefficient of z^1 in K
		t0 = t.moment(0)
		T = PowerSeriesRing(QQ,'ww',default_prec=deg)
		err = self.zero_elt().lift_to_dist_fam(deg,r,w)

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

		mu = t.solve_diff_eqn()
		print((mu.act_right(Matrix(2,2,[1,1,0,1]))-mu-t).normalize())

		v = [mu.scale(-1)] + v
	
		Phis = modsym_dist_fam(self.level(),v,self.manin)

		return Phis

#	def check_loop(self):
#		return self.ms().check_loop().normalize()

	def is_Tq_eigen(self,q,verbose=false):
		p = self.data[0].p
		M = self.data[0].num_moments()

		a = 0
		m = 0
		done = false
		while (self.data[a].moment(m) % (p^M) == 0) and (not done):
			if a < self.ngens() - 1:
				a = a + 1
			else:
				if m < self.num_moments() - 1:
					m = m + 1
				else:
					done = True
		if done:
			if verbose:
				print("The symbol is 0")
			return 0
		else:
			Phiq = self.hecke(q)
			c = Phiq.data[a].moment(m)/self.data[a].moment(m)
			if verbose:
				print(Phiq - self.scale(c))
			return c % (p^(M-m-self.valuation())),(Phiq-self.scale(c)).valuation()
		
	def vector_of_total_measures(self):
		"""returns the vector comprising of the total measure of each distribution defining Phi"""
		v=[]
		for j in range(0,self.ngens()):
			v=v+[self.data[j].moments[0]]
		return v

	def vector_of_total_measures_mod_pn(self,n):
		"""returns the vector comprising of the total measure of each distribution defining Phi"""
		v=[]
		R=Integers(self.p()^n)
		for j in range(0,self.ngens()):
			v=v+[R(self.data[j].moments[0])]
		return v


	def project_to_ordinary_subspace(self):
		"""Iterates U_p M+1 times where M is the number of moments"""
		p = self.p()
		Phi = self
		for r in range(self.num_moments()*2):
#			print((r,self.num_moments()*2))
			Phi = Phi.hecke(p)

		return Phi

	def up(self,p,beta):
		"""For a critical slope symbol with U_p-eigenvalue beta, returns Phi | U_p / beta without loss of accuracy

		ONLY CODED FOR WEIGHT 2"""
		if self.full_data == 0:
			self.compute_full_data_from_gen_data()
		psi = self.zero()

		# acts by U_p/beta but with no normalizations.  This gives the correct answer for higher moments but not 0th-moments
		for a in range(0,p): 
			temp = self.act_right_wo_normalize(Matrix(ZZ,[[1,a],[0,p]]))
			psi = psi.add_wo_normalizing(temp)
		psi = psi.scale(1/beta)

		# This code corrects the 0-th moments assuming that the specialization of self is U_p-eigen with eigenvalue beta
		for d in range(0,len(self.data)):
			mu = psi.data[d]
			mu.change_nth_moment(0,self.data[d].moment(0))
		return psi.normalize()

	def up_by_poly(self,p,beta,f,verbose=false):
		v=f.padded_list()
		act = [self]
		for j in range(len(v)-1):
			if verbose:
				print(j,"out of",len(v)-2)
			act += [act[len(act)-1].up(p,beta)]
		ans = self.zero()
		for j in range(len(v)):
			ans += act[j].scale(v[j])
		return ans

	#@cached_function
	def phi_on_Da(self,a,D):
		p=self.p()
		ans=self.zero_elt()
		for b in range(1,abs(D)+1):
			if gcd(b,D)==1:	
				ans=ans+self.eval(Matrix(2,2,[1,b/abs(D),0,1])*Matrix(2,2,[a,1,p,0])).act_right(Matrix(2,2,[1,b/abs(D),0,1])).scale(kronecker(D,b)).normalize()
		return ans.normalize()

	#@cached_function
	def basic_integral(self,a,j,ap,D):
		"""returns int_{a+pZ_p} (z-{a})^j dPhi(0-infty) -- see formula [PS, sec 9.2] """
		M=self.num_moments()
		p=self.p()
		ap=ap*kronecker(D,p)
		ans=0
		for r in range(j+1):
			ans=ans+binomial(j,r)*(a-teich(a,p,M))^(j-r)*p^r*self.phi_on_Da(a,D).moment(r)
		return ans/ap




	# def up(self,p,beta):
	# 	"""For a critical slope symbol, return Phi | U_p / beta without loss of accuracy

	# 	ONLY CODED FOR WEIGHT 2"""
	# 	p = self.p()
	# 	Phi = self
	# 	if self.full_data==0:
	# 		self.compute_full_data_from_gen_data()
	# 	v=[]
	# 	for d in range(0,len(self.data)):
	# 		D=self.manin.mats[d]
	# 		PhiDas = [Phi.eval(Matrix(2,2,[1,a,0,p])*D) for a in range(p)]
	# 		mu = Phi.data[0].zero()
	# 		moments = []
	# 		t = mu.num_moments()
	# 		for j in range(1,t):
	# 			ans = 0
	# 			for a in range(p):
	# 				for r in range(0,j):
	# 					ans = ans + binomial(j,r) * a^(j-r) * p^r / beta * PhiDas[a].moment(r)
	# 			moments += [ans]
	# 		moments = [Phi.eval(D).moment(0)] + moments # add back on 0th momment which is preserved by U_p/beta
	# 		mu.moments = moments
	# 		v += [mu]

	# 	C=type(self)		
	# 	return C(self.level,v,self.manin).normalize()



	
def random_OMS(N,p,k,M,char=trivial_character(1)):
	"""Returns a random OMS with tame level N, prime p, weight k, and M moments"""
	## There must be a problem here with that +1 -- should be variable depending on a c of some matrix
	if k != 0:
		M = M + valuation(k,p) + 1 + floor(log(M)/log(p)) ## We'll need to divide by some power of p and so we add extra accuracy here.

	manin = manin_relations(N*p)
	v = []

#this loop runs thru all of the generators (except (0)-(infty)) and randomly chooses a distribution to assign  to this generator (in the 2,3-torsion cases care is taken to satisfy the relevant relation)
	for j in range(1,len(manin.gens)):
		rj = manin.gens[j]
		if (manin.twotor.count(rj) != 0):
			gam = manin.gen_rel_mat(j)
			mu=random_dist(p,k,M,char)
			v=v+[(mu-mu.act_right(gam))]
		elif (manin.threetor.count(rj)!=0):
			gam = manin.gen_rel_mat(j)
			mu=random_dist(p,k,M,char)
			v=v+[(mu.scale(2)-mu.act_right(gam)-mu.act_right(gam^2))]
		else:
			v=v+[random_dist(p,k,M,char)]

#now we compute nu_infty of Prop 5.1 of [PS1]
	t=v[0].zero()
	for j in range(1,len(manin.gens)):
		rj = manin.gens[j]
		if (manin.twotor.count(rj) == 0) and (manin.threetor.count(rj) == 0):
			t = t + v[j-1].act_right(manin.gen_rel_mat(j)) - v[j-1]
		else:
			t = t - v[j-1]
		
## If k = 0, then t has total measure zero.  However, this is not true when k != 0  
## (unlike Prop 5.1 of [PS1] this is not a lift of classical symbol).  
## So instead we simply add (const)*mu_1 to some (non-torsion) v[j] to fix this
## here since (mu_1 |_k ([a,b,c,d]-1))(trival char) = chi(a) k a^{k-1} c , 
## we take the constant to be minus the total measure of t divided by (chi(a) k a^{k-1} c)

	if k != 0:
		j = 1
		rj = manin.gens[j]
		while (j < len(manin.gens)-1) and ((manin.twotor.count(rj) != 0) or (manin.threetor.count(rj) != 0)):
			j = j + 1
			rj = manin.gens[j]
			print(j)
		assert j < len(manin.gens) - 1, "Everything is 2 or 3 torsion!  NOT YET IMPLEMENTED IN THIS CASE"

		gam = manin.gen_rel_mat(j)
		a = gam[0,0]
		c = gam[1,0]
		
		if char != None:
			chara = char(a)
		else:
			chara = 1
		err = -t.moments[0]/(chara*k*a^(k-1)*c)
		mu_1 = v[rj-1].zero()
		mu_1.moments[1] = err
		v[j-1] = v[j-1] + mu_1
		t = t + mu_1.act_right(gam) - mu_1
		
	mu = t.solve_diff_eqn()
	v = [mu.scale(-1)] + v
	Phi = modsym_dist(N*p,v,manin)	
#	if k != 0:
#		e = -Phi.valuation()
#		Phi = Phi.scale(p^e).change_precision(M-e)
	return Phi

## NOT YET REWRITTEN AS ABOVE
def random_OMS_char(N,p,k,chi,M):
	"""Returns a random OMS with tame level N, prime p, weight k, and M moments --- requires no 2 or 3-torsion"""
	manin=manin_relations(N*p)
	v=[]
	for j in range(1,len(manin.gens)):
		g=manin.gens[j]
		gam=manin.glue[g][1]
		a=gam[0,0]
		c=gam[1,0]
		if manin.twotor.count(g)==0:
			mu=random_dist_char(p,k,chi,M).zero()
			mu.moments[0]=c
			mu.moments[1]=(chi(a)-a)*a/chi(a)  #formula to force difference equation to work 
			v=v+[mu]
		else:
			v=v+[random_dist_char(p,k,chi,M).zero()]
#			rj=manin.twotor.index(g)
#			gam=manin.twotorrels[rj]
#			mu=random_dist_char(p,k,chi,M)
#			v=v+[(mu.act_right(gam)-mu).scale(1/2)]
	t=v[0].zero()
	for j in range(2,len(manin.rels)):
		R=manin.rels[j]
		if len(R)==1:
			if R[0][0]==1:
				rj=manin.gens.index(j)
				t=t+v[rj-1]
				print(v[rj-1])
			else:
				index=R[0][2]
				rj=manin.gens.index(index)
				mu=v[rj-1]
				print(mu.act_right(R[0][1]).scale(R[0][0]).normalize())
				t=t+mu.act_right(R[0][1]).scale(R[0][0])
	t=t.normalize()
	mu=t.solve_diff_eqn()
	v=[mu.scale(-1)]+v

	return modsym_dist(N*p,v,manin)	

def random_ordinary_OMS(N,p,k,M,char=None):
	Phi = random_OMS(N,p,k,M,char)
#	print("first check",Phi.check_loop().normalize())
	Phi = Phi.project_to_ordinary_subspace()
#	print("second check",Phi.check_loop().normalize())
	Phi = Phi.change_precision(M)

	return Phi

## U_p is iterated r times and the resulting list of vectors of moments is returned
def hecke_span(Phi,q,r):
	p = Phi.p()
	M = Phi.num_moments()

	Psi = Phi
	list = []
	list = list + [Psi.vector_of_total_measures()]
	for j in range(r):
		Psi = Psi.hecke(q)
		list = list + [Psi.vector_of_total_measures()]
	
	A=Matrix(list)
	
	return list,A,(A.echelon_form())%(p^M)
