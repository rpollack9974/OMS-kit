class modsym_symk(modsym):
	def ms(self):
		"""demotes to a regular modular symbol"""
		return modsym(self.level(),self.data,self.manin)

	def weight(self):
		"""returns the weight of any value of self"""
		return self.data[0].weight

	def base_ring(self):
		return self.data[0].base_ring

	def chi(self):
		return self.data[0].chi

	def valuation(self,p,remove_binom=true):
		"""returns the valuation of self at p -- i.e. the exponent of the largest power of p which divides all of the coefficients of all values of self"""
		v=self.data
		return min([v[j].valuation(p,remove_binom=remove_binom) for j in range(0,len(v))])

	def filtration(self,p,remove_binom=true):
		v = self.data 
		return min([v[j].filtration(p,remove_binom=remove_binom) for j in range(0,len(v))])

	def is_zero(self):
		j = 0
		ans = True
		while ans and j<self.ngens():
			ans = self.data[j].is_zero()
			j = j + 1
		return ans

	def p_stabilize(self,p,alpha):
		"""p-stablizes self to form an eigensymbol for U_p with eigenvalue alpha"""
		N=self.level()
		assert N%p!=0, "The level isn't prime to p"

		pp=Matrix(ZZ,[[p,0],[0,1]])
		manin=manin_relations(N*p)
		v=[]
		for j in range(0,len(manin.gens)):
			rj=manin.gens[j]
			v=v+[self.eval(manin.mats[rj])-self.eval(pp*manin.mats[rj]).act_right(pp).scale(1/alpha)]
		return modsym_symk(N*p,v,manin)

	def p_stabilize_ordinary(self,p,ap,M):
		"""returns the unique p-ordinary p-stabilization of self"""
		N=self.level()
		k=self.data[0].weight
		assert N%p!=0, "The level isn't prime to p"
		assert ap%p!=0, "Not ordinary!"

		"""makes alpha the unit root of Hecke poly"""
		R=PolynomialRing(pAdicField(p,M),'y') 
		y=R.gen()
		f=y^2-ap*y+p^(k+1)
		v=f.roots()
		if Integer(v[0][0])%p!=0:
			alpha=Integer(v[0][0])
		else:
			alpha=Integer(v[1][0])

		if self.full_data == 0:
			self.compute_full_data_from_gen_data()

		return self.p_stabilize(p,alpha)

	def p_stabilize_critical(self,p,ap,M):
		N=self.level()
		assert N%p!=0, "The level isn't prime to p"
		assert ap%p!=0, "Not ordinary!"

		"""makes alpha the non-unit root of Hecke poly"""
		R=PolynomialRing(Qp(p,M),'y') 
		y=R.gen()
		f=y**2-ap*y+p
		v=f.roots()
		if Integer(v[0][0])%p==0:
			alpha=Integer(v[0][0])
		else:
			alpha=Integer(v[1][0])

		if self.full_data == 0:
			self.compute_full_data_from_gen_data()

		return self.p_stabilize(p,alpha)

	def is_Tq_eigen_old(self,q,p,M):
		"""determines of self is an eigenvector for T_q modulo p^M"""
		selfq=self.hecke(q)
		r=0
		while ((self.data[r].coef(0))==0) and (r<=self.ngens()):
			r=r+1
		if r>self.ngens():
			#all coefficients of Y^k are zero which I think forces it not to be eigen
			return False
		else:	
			c=selfq.data[r].coef(0)/self.data[r].coef(0)
			val=(selfq-self.scale(c)).valuation(p)
			if val>=M:
				return True,c
			else:
				return False

	def is_Tq_eigen(self,q):
		"""determines of self is an eigenvector for T_q"""
		if self.is_zero():
			return False
		else:
			selfq = self.hecke(q)
			r = 0
			while self.data[r].is_zero():
				#print(r,self.data[r],self.data[r].is_zero())
				r += 1
			c = 0
			while self.data[r].coef(c) == 0:
				c += 1
			ev = selfq.data[r].coef(c) / self.data[r].coef(c)
			return (selfq - self.scale(ev)).is_zero(),ev

	def is_Tq_eigen_mod(self,q,p,M):
		"""determines of self is an eigenvector for T_q modulo p^M"""
		selfq=self.hecke(q)
		r=0
		while ((self.data[r].coef(0))%(p)==0) and (r<=self.ngens()):
			print(r)
			r=r+1
		if r>self.ngens():
			#all coefficients of Y^k are zero which I think forces it not to be eigen
			#THIS CANT BE RIGHT MOD P!!!
			return False
		else:	
			c=selfq.data[r].coef(0)/self.data[r].coef(0)
			val=(selfq-self.scale(c)).valuation(p)
			if val>=M:
				return True,c
			else:
				return False

	def int_against_poly(self,P,a,m):
		"""returns int_\infty^{-a/m} f(z)P(z) dz --- ignoring pi's, periods and such"""
		D = Matrix(2,2,[1,-a,0,m])
		k = self.data[0].weight
		v = P.padded_list()
		while len(v) < k+1:
			v += [0]
		phiD = self.eval(D)
		return sum([v[i] * phiD.coef(i) / binomial(k,i) for i in range(k+1)])

	def lamb(self,P,a,m):
		"""returns lambda(f,P,a,m) as in MTT"""
		z = P.parent().gen()
		P = P.substitute(m*z+a)
		return self.int_against_poly(P,a,m)

	def lamb_twist(self,r,b,n,twist):
		"""returns lambda(f_chi,(mz)^r,b,n) as in MTT where f_chi is quad twist by twist"""
		R.<z>=PolynomialRing(QQ)
		ans = 0 
		for a in range(abs(twist)):
			if gcd(a,twist)==1:
				ans += kronecker_symbol(twist,a) * self.lamb(z^r,twist*b-n*a,twist*n)
		return ans

	def lamb_twist_poly(self,P,b,n,twist):
		ans = 0
		for i in range(P.degree()+1):
			ans += P[i] * self.lamb_twist(i,b,n,twist)
		return ans

	def MazurTate(self,p,n,acc,h=0,twist=1,verbose=false):
		assert p>2,"p=2 not coded"
		k = self.data[0].weight
		Qp = pAdicField(p,acc)
		teich = Qp.teichmuller_system()
		RR.<z>=PolynomialRing(QQ)
		gam = 1 + p
		if ceil(h) == h:
			h += 1
		else:
			h = ceil(h)
		R.<T> = PolynomialRing(self.base_ring())
		oneplusTpower = R(1)
		LOGS = [1]
		logp_gam = ZZ(logp_fcn(p,h*p^n+2,gam)) 
		log_factor = logp(p,T,h*p^n+2) / logp_gam ## log_factor is log_gamma(1+T)

		for c in range(h):
			LOGS += [LOGS[len(LOGS)-1] * (log_factor - c)]

		oneplusTpower = [1]
		for j in range(p^n):
			oneplusTpower += [oneplusTpower[len(oneplusTpower)-1] * (1+T)]  #oneplusTpower[j] = (1+T)^j

		ans = R(0)
		for i in range(h):
			for j in range(p^n):
				if verbose:
					print((i,j))
				for a in range(1,p):
					b = gam^j * ZZ(teich[a-1])
					ans += oneplusTpower[j] * LOGS[i] * self.lamb_twist_poly((z-b)^i,b,p^(n+1),twist) / (b^i * factorial(i))
		return ans


	def pL_newton(self,p,n,pp):
		mt = self.MazurTate(p,n,20)
		v = mt.coefficients()
		if pp.base_ring() != ZZ:
			hull = [(i,v[i].valuation(pp)/pp.absolute_ramification_index()) for i in range(len(v))]
		else:
			hull = [(i,v[i].valuation(pp)) for i in range(len(v))]
		hull.reverse()
		ans = NewtonPolygon(hull).slopes()
		return [-a for a in ans]


	def lift_to_OMS(self,p,M):
		"""returns a (p-adic) overconvergent modular symbols with M moments which lifts self up to an Eisenstein error"""
		v=[]
		## this loop runs through each generator and lifts the value of self on that generator to D
		for j in range(1,len(self.manin.gens)):
			rj = self.manin.gens[j]
			if (self.manin.twotor.count(rj) == 0) and (self.manin.threetor.count(rj) == 0):
				v = v + [self.data[j].lift_to_dist(p,M)]
			elif (self.manin.twotor.count(rj) != 0):
				## Case of two torsion (See [PS] section 4.1)
				gam = self.manin.gen_rel_mat(j)
				mu = self.data[j].lift_to_dist(p,M)
				v = v + [(mu - mu.act_right(gam)).scale(1/2)]
			else:
				## Case of three torsion (See [PS] section 4.1)	
				gam = self.manin.gen_rel_mat(j)
				mu = self.data[j].lift_to_dist(p,M)
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

		mz=t.normalize().moment(0)
		print('Total measure=',mz,'valuation=',mz.valuation(p))
#		assert t.normalize().moment(0) == 0, "Not total measure 0 in lifting OMS" 

		mu = t.solve_diff_eqn()

		v = [mu.scale(-1)] + v
	 
		return modsym_dist(self.level(),v,self.manin)	

	def lift_to_OMS_eigen(self,p,M,ap=None,verbose=True):
		"""returns Hecke-eigensymbol OMS lifting phi -- phi must be a p-ordinary eigensymbol"""
		if ap == None:
			v=self.is_Tq_eigen_mod(p,p,M)
			assert v[0], "not eigen at p!"
			ap=v[1]
		k=self.weight()
		Phi=self.lift_to_OMS(p,M)
		s=-Phi.valuation()
		if s>0:
			if verbose:
				print("Scaling by ",p,"^",s)
			Phi=Phi.scale(p^(-Phi.valuation()))
		Phi=Phi.normalize()
		if verbose:
			print("Applying Hecke")
		Phi=Phi.hecke(p).scale(1/ap)
		if verbose:
			print("Killing eisenstein part")
		if (ap%(p^M))!=1:
			Phi=(Phi-Phi.hecke(p)).scale(1/(1-ap))
			e=(1-ap).valuation(p)
			if e>0:
				Phi=Phi.change_precision(M-e)
				if verbose:
					print("change precision to",M-e)
		else:
			q=2
			v=self.is_Tq_eigen_mod(q,p,M)
			assert v[0],"not eigen at q"
			aq=v[1]
			while (q!=p) and (aq-q^(k+1)-1)%(p^M)==0:
				q=next_prime(q)
				v=self.is_Tq_eigen_mod(q,p,M)
				assert v[0],"not eigen at q"
				aq=v[1]
			Phi=(Phi.scale(q^(k+1)+1)-Phi.hecke(q)).scale(1/(q^(k+1)+1-aq))
			e=(q^(k+1)+1-aq).valuation(p)
			if e>0:
				Phi=Phi.change_precision(M-e)
				print("change precision to",M-e)
		if verbose:
			print("Iterating U_p")
		Psi=Phi.hecke(p).scale(1/ap)
		err=(Psi-Phi).valuation()
		Phi=Psi
		while err<Infinity:
			if (Phi.valuation()>=s) and (s>0):
				Phi=Phi.scale(1/p^s)
				Phi=Phi.change_precision(Phi.num_moments()-s).normalize()
				print("unscaling by p^",s)
				s=Infinity
			Psi=Phi.hecke(p).scale(1/ap)
			err=(Psi-Phi).valuation()
			if verbose:
				print("error is zero modulo p^",err)
			Phi=Psi
		return Phi.normalize()

	"""self is a modular symbol taking values in Sym^k(K^2), where K is a finite extension of Q, psi is a map from the K to Qp and the below function 'map' applies psi to all polynomial coefficients and then lifts them to QQ"""
	def map(self,psi):
		v=[self.data[j].map(psi) for j in range(len(self.data))]
		return modsym_symk(self.level(),v,self.manin)

	"""simply apply psi to self"""
	def map2(self,psi):
		v=[self.data[j].map2(psi) for j in range(len(self.data))]
		for j in range(self.ngens()):
			v[j].chi = compose(psi,v[j].chi)
		return modsym_symk(self.level(),v,self.manin)

	def coerce_to_Qp(self,p,M,verbose=false):
		"""If K is the base_ring of self, this function takes all maps K-->Q_p and applies them to self return a vector of <modular symbol,map:K-->Q_p> as map varies over all such maps.  M is the accuracy"""
		K=self.base_ring()
		if K == QQ:
			i = QQ.hom(pAdicField(p,M))
			return [[self.map(i),i]]
		else:
			f=K.defining_polynomial()	
			R.<x>=PolynomialRing(pAdicField(p,M+10))
			v=R(f).roots()
			if len(v)==0:
				if verbose:
					print("No coercion possible -- no prime over p has degree 1")
				return []
			else:
				ans=[]
				for j in range(len(v)):
					root=v[j][0]
					psi=K.hom([root],pAdicField(p,M))
					ans=ans+[[self.map(psi),psi]]
			return ans

	def coerce_via_map(self,psi):
		"""If K is the base_ring of self, this function takes all maps K--> L and applies them to self return a vector of <modular symbol,map:K-->Q_p> as map varies over all such maps.  M is the accuracy"""
		K=self.base_ring()
		ans=[]
		for j in range(len(v)):
			ans=ans+[[self.map(psi),psi]]
		return ans


	def lift(self,p,ap):
		"""M.Greenberg method of lifting one step at a time -- slower in these programs because of how I optimized things"""
		k=self.weight()
		ans=[]
		for a in range(self.ngens()):
			v=[]
			for j in range(k+1):
				v=v+[phi.data[a].coef(j)]
			v=dist(p,k,vector(v+[0]))
			ans=ans+[v]	
		new=modsym_dist(self.level(),ans,self.manin)
		return new.hecke(p).scale(1/ap).normalize()

	#returns mu_f(a+p^nZp) with accuracy p^M
	def measure(self,a,p,n,ap,M,alpha=None):
		"""returns the value of the measure mu_f(a+p^nZp)"""
		assert ap.valuation(p)==0,"Only coded in ordinary case"
		assert self.weight()==0,"Only coded in weight 2"

		if alpha == None:
			R.<x>=PolynomialRing(pAdicField(p,M))
			rs = (x^2-ap*x+p).roots()
			if rs[0][0].valuation() == 0:
				alpha = QQ(rs[0][0])
			else:
				alpha = QQ(rs[1][0])

		return 1/alpha^n * self.eval(Matrix(2,2,[a,1,p^n,0])).coef(0) - 1/alpha^(n+1) * self.eval(Matrix(2,2,[a,1,p^(n-1),0])).coef(0)

	def measure_twist(self,a,p,n,ap,M,D,alpha=None):
		"""returns the value of the measure mu_f(a+p^nZp)"""
#		assert ap.valuation(p)==0,"Only coded in ordinary case"
		assert self.weight()==0,"Only coded in weight 2"

		if alpha == None:
			R.<x>=PolynomialRing(pAdicField(p,M))
			if ap%p != 0:
				rs = (x^2-ap*x+p).roots()
				if rs[0][0].valuation() == 0:
					alpha = QQ(rs[0][0])
				else:
					alpha = QQ(rs[1][0])
			else:
				Qp = R.base_ring()
				L.<alpha> = Qp.ext(x^2-ap*x+p)

		ans = 0

		for b in range(abs(D)):
			ans += kronecker_symbol(D,b) * 1/alpha^n * self.eval(Matrix(2,2,[1,b/abs(D),0,1])*Matrix(2,2,[a,1,p^n,0])).coef(0) - 1/alpha^(n+1) * self.eval(Matrix(2,2,[1,b/abs(D),0,1])*Matrix(2,2,[a,1,p^(n-1),0])).coef(0)

		return ans

	def pLfunc_val(self,c,val,p,ap,n,M,D=1,alpha=None):
		"""returns the value of L_p(omega^c,T) at T=val around mod p^n"""
		ans = 0
		for a in range(1,p):
			for j in range(p^(n-1)):
				ans += teich(a,p,M)^c * (val+1)^j * self.measure_twist(teich(a,p,M)*(1+p)^j,p,n,ap,M,D,alpha=alpha)

		return ans


def form_modsym_from_elliptic_curve(E):
	"""returns the modular symbol (in the sense of Stevens) associated to E"""
	N=E.conductor()
	q = 3
	while N % (q^2) == 0:
		q = next_prime(q)
	L=E.padic_lseries(q)
	manin=manin_relations(N)
	v=[]
	R.<X,Y>=PolynomialRing(QQ,2)
	for j in range(0,len(manin.gens)):
		rj=manin.gens[j]
		g=manin.mats[rj]
		a=g[0,0]
		b=g[0,1]
		c=g[1,0]
		d=g[1,1]
		if c!=0:
			a1=L.modular_symbol(a/c,1)+L.modular_symbol(a/c,-1)
		else:
			a1=L.modular_symbol(oo,1)+L.modular_symbol(oo,-1)
		if d!=0:
			a2=L.modular_symbol(b/d,1)+L.modular_symbol(b/d,-1)
		else:
			a2=L.modular_symbol(oo,1)+L.modular_symbol(oo,-1)
		v=v+[symk(0,R(a1))-symk(0,R(a2))]
	return modsym_symk(N,v,manin)

def form_modsym_from_decomposition(A):
	"""A is a piece of the result from a command like ModularSymbols(---).decomposition()"""
	M=A.ambient_module()
	N=A.level()
	k=A.weight()
	manin=manin_relations(N)
	chi=M.character()
	if chi.order()==1:
		chi = None

	w=A.dual_eigenvector()
	K=w.parent().base_field()
	v=[]
	R.<X,Y>=PolynomialRing(K,2)
	for s in range(0,len(manin.gens)):
		rs=manin.gens[s]
		g=manin.mats[rs]
		a=g[0,0]
		b=g[0,1]
		c=g[1,0]
		d=g[1,1]
		ans=0
		if c!=0:
			r1=a/c
		else:
			r1=oo
		if d!=0:
			r2=b/d
		else:
			r2=oo
		for j in range(k-1):
			coef=w.dot_product(M.modular_symbol([j,r1,r2]).element())
			ans=ans+X^j*Y^(k-2-j)*binomial(k-2,j)*coef
		v=v+[symk(k-2,poly=ans,base_ring=K,chi=chi)]
	return modsym_symk(N,v,manin)

def form_modsym_from_decomposition_padic(A,p,acc,dual_evector=None,roots=None):
	"""A is a piece of the result from a command like ModularSymbols(---).decomposition()
	This function then returns a list of modular symbols, one for each embedding of the
	Hecke field of A into Qp with accuracy p^M"""
	M=A.ambient_module()
	N=A.level()
	k=A.weight()
	manin=manin_relations(N)
	chi=M.character()

	if dual_evector==None:
		w=A.dual_eigenvector()
	else:
		w=dual_evector
	K=w.parent().base_field()
	Qp=pAdicField(p,acc)
	R.<X,Y>=PolynomialRing(Qp,2)
	RR.<x>=PolynomialRing(Qp)
	f=K.defining_polynomial()
	if roots==None:
		roots=RR(f).roots()
		roots=[roots[a][0] for a in range(len(roots))]			
	print("---There are ",len(roots)," root(s).")

	answers=[]
	for root in roots:
		print("----using ",root)
		psi=K.hom([root],Qp)
		v=[]
		for s in range(0,len(manin.gens)):
			rs=manin.gens[s]
			g=manin.mats[rs]
			a=g[0,0]
			b=g[0,1]
			c=g[1,0]
			d=g[1,1]
			ans=0
			if c!=0:
				r1=a/c
			else:
				r1=oo
			if d!=0:
				r2=b/d
			else:
				r2=oo
			for j in range(k-1):
#				print((s,j))
				t=M.modular_symbol([j,r1,r2]).element()
				coef=sum([t[a]*psi(w[a]) for a in range(len(t))])
	##			print i
	#			print 'coef=',coef
	#			print 'XY=',X^i*Y^(k-2-i)*binomial(k-2,i)
	#			print 'ki=',k,i
	#			print 'extra=',X^i*Y^(k-2-i)*binomial(k-2,i)*coef
	#			print "-----"
				ans=ans+X^j*Y^(k-2-j)*binomial(k-2,j)*coef
	#			print 'ans=',ans
	#			print "*****"
			v=v+[symk(k-2,poly=ans,base_ring=Qp,chi=chi)]
		answers+=[modsym_symk(N,v,manin)]
	return answers

def form_modsym_from_decomposition_padic_enhanced(A,p,acc,dual_evector_padic):
	"""A is a piece of the result from a command like ModularSymbols(---).decomposition()
	This functions returns a p-adic modular symbol based on dual_evector_padic"""
	M=A.ambient_module()
	N=A.level()
	k=A.weight()
	manin=manin_relations(N)
	chi=M.character()

	Qp=pAdicField(p,acc)
	R.<X,Y>=PolynomialRing(Qp,2)
	w=dual_evector_padic

	v=[]
	for s in range(0,len(manin.gens)):
		rs=manin.gens[s]
		g=manin.mats[rs]
		a=g[0,0]
		b=g[0,1]
		c=g[1,0]
		d=g[1,1]
		ans=0
		if c!=0:
			r1=a/c
		else:
			r1=oo
		if d!=0:
			r2=b/d
		else:
			r2=oo
		for j in range(k-1):
			t=M.modular_symbol([j,r1,r2]).element()
			coef=sum([t[a]*w[a] for a in range(len(t))])
##			print i
#			print 'coef=',coef
#			print 'XY=',X^i*Y^(k-2-i)*binomial(k-2,i)
#			print 'ki=',k,i
#			print 'extra=',X^i*Y^(k-2-i)*binomial(k-2,i)*coef
#			print "-----"
			ans=ans+X^j*Y^(k-2-j)*binomial(k-2,j)*coef
#			print 'ans=',ans
#			print "*****"
		v=v+[symk(k-2,poly=ans,base_ring=Qp,chi=chi)]
	return modsym_symk(N,v,manin)

## brutally converts a modular symbol defined over Zp to one defined over Z.
def convert_modsym_padic_to_integral(phi):
	RR.<X,Y>=PolynomialRing(ZZ)
	for a in range(len(phi.data)):
		phi.data[a].poly=RR(phi.data[a].poly)
	return "Done"

def a(r1,r2):
	ans=0
	for j in range(k-1):
		coef=w.dot_product(M.modular_symbol([j,r1,r2]).element())
		ans=ans+X^j*Y^(k-2-j)*binomial(k-2,j)*coef
	return ans	

def boundary(N,q):
	manin = manin_relations(N)
	R.<X,Y>=PolynomialRing(QQ,2)
	v = []
	for a in manin.gens:
		n = R(0)
		m = R(0)
#		print(a,ZZ(manin.mats[a][1,0]),q,ZZ(manin.mats[a][1,0]) % q)
		if ZZ(manin.mats[a][1,0]) % q == 0:
			n = 1
		if ZZ(manin.mats[a][1,1]) % q == 0:
			m = 1
		v += [symk(0,n-m)]
	return modsym(N,v,manin)


def mu(P,w):
	return min([w(P[a]) for a in range(P.degree()+1)])

def lamb(P,w):
	m = mu(P,w)
	v = [w(P[a]) for a in range(P.degree()+1)]
	return v.index(m)	