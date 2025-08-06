class modsym_measures(modsym):
	def ms(self):
		"""demotes to a regular modular symbol"""
		return modsym(self.level,self.data,self.manin)

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

	def check_loop(self):
		return self.ms().check_loop().normalize()

	def vector_form(self):
		"""returns the vector of [Phi(D_i)]"""
		return [self.data[j] for j in range(1,self.ngens())]

		###SHOULD CHANGE THIS TO A FUNCTION AND SAME FOR THE MEASURES
	def decrease_accuracy(self,M):
		for j in range(self.ngens()):
			self.data[j].decrease_accuracy(M)

	def measure_to_distribution(self):
		data = []
		for j in range(self.ngens()):
			data += [self.data[j].measure_to_distribution()]
		return modsym_dist(self.level,data,self.manin)

	def valuation(self):
		"""returns the exponent of the highest power of maximal containing all values"""
		return min([self.data[j].valuation() for j in range(0,len(self.data))])


	def clear_powers(self):
		"""divides by w^valuation and renormalizes"""
		w = self.data[0].Mahler_coef(0).parent().gen()
		M = self.data[0].num_coefs()
		v = self.valuation()
		for j in range(len(self.data)):
			for i in range(M):
				self.data[j].Mahler_coefs[i] = self.data[j].Mahler_coefs[i].quo_rem(w^v)[0]
		self.decrease_accuracy(M-v)


	def pLfunction(self,verbose=False):		
		R.<T> = PowerSeriesRing(self.data[0].base_ring)
		p = self.p()
		ans = R(0)
		M = self.data[0].num_coefs()
		logp_gam = ZZ(logp_fcn(p,2*M,1+p))
		mus = [self.eval(Matrix(2,2,[1,a,0,p])) for a in range(p)]
		for n in range(M):
			cn = 0
			for a in range(1,p):
				mua = mus[a]
				for m in range(M):
					if verbose:
						print (n,a,m),"out of",(M,p,M)
					if type(self.data[0].k)==type(1):		
						cm = sum([(-1)^(m-i)*B(m,i)*B(ZZ(logp_fcn(p,2*M,(a+p*i)/teich(a,p,2*M))/logp_gam),n) for i in range(m+1)])
					else:		
						cm = sum([(-1)^(m-i)*Bp(m,i,p)*Bp(ZZ(logp_fcn(p,2*M,(a+p*i)/teich(a,p,2*M))/logp_gam),n,p) for i in range(m+1)])
					cn += cm * mua.Mahler_coef(m)
			ans += cn * T^n
		return ans


def vector_to_modsym(N,p,v):
	"""Given a vector v of length t of measurs_on_Zp returns Phi such that Phi(D_i) = v[i]
		except for i with torsion index and one i to satisfy difference equation
	"""
	manin = manin_relations(N*p)
	#assert len(manin.twotor)==0 and len(manin.threetor)==0, "level must be torsion-free" 
	if not (len(manin.twotor)==0 and len(manin.threetor)==0):
		print "Level not torsion-free!"

#now we compute nu_infty of Prop 5.1 of [PS1] (except we have functions here)
	t=v[0].zero()
	for j in range(1,len(manin.gens)):
		t = t + v[j-1].act_right(manin.gen_rel_mat(j)) - v[j-1]

	d = len(manin.gens)
	if v[0].k != 0:
		err = t.Mahler_coef(0)
		temp = v[0].zero()
		temp.Mahler_coefs[1] = 1
		C = manin.gen_rel_mat(d-1)
		new = (temp.act_right(C)-temp).Mahler_coef(0)
		nu = temp.scale(-err/new)
		v[d-2] = v[d-2] + nu
		t = t + nu.act_right(C) - nu
	f=t.solve_diff_eqn()
	v=[f.scale(-1)]+v

	Phi = modsym_measures(N*p,v,manin)	
	return Phi

