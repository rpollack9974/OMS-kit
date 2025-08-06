class modsym_cont_fcns(modsym):
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


class modsym_cont_fcn_to_Lambda(modsym_cont_fcns):
	def valuation(self):
		"""returns the exponent of the highest power of maximal containing all values"""
		return min([self.data[j].valuation() for j in range(0,len(self.data))])



def vector_to_modsym(N,p,v):
	"""Given a vector v of length t of cont_fcns_to_Zp returns Phi such that Phi(D_i) = v[i]; assumes torsion-free level"""
	manin = manin_relations(N*p)
	assert len(manin.twotor)==0 and len(manin.threetor)==0, "level must be torsion-free" 

#now we compute nu_infty of Prop 5.1 of [PS1] (except we have functions here)
	t=v[0].zero()
	for j in range(1,len(manin.gens)):
		t = t + v[j-1].act_right(manin.gen_rel_mat(j)) - v[j-1]

	d = len(manin.gens)
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

	Phi = modsym_cont_fcns(N*p,v,manin)	
	return Phi

