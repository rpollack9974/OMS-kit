from sage.structure.sage_object import SageObject

#################################################################################################################
##  A continuous function f:Z_p-->R with R a p-adic ring has a Mahler expansion f = sum_n a_n (x choose n) 
##  where {a_n} is a sequence in R converging to 0.  We represent such a function by the sequence {a_n} (or
##  at least some approximation of this sequence to be determined later).
#################################################################################################################

class cont_fcn_on_Zp(SageObject):
	def __init__(self,p,R,coefs):
		"""
		Initializes the R-valued function 

		INPUT:
			- p -- prime number
			- R -- p-adic ring where the functions take value
			- Mahler_coefs -- a vector of elements of R which represents the Mahler coefficients

		OUTPUT:

		The continuous fcn f:Z_p --> R such thay f = sum_n Mahler_coefs[n] (x choose n)
	
		"""
		self.p=p
		self.base_ring = R
		coefs = [R(coefs[a]) for a in range(len(coefs))]
		self.Mahler_coefs = vector(coefs)

	def __repr__(self):
		return repr(self.Mahler_coefs)

	def base_ring(self):
		return self.base_ring

	def Mahler_coef(self,n):
		return self.Mahler_coefs[n]

	def num_coefs(self):
		return len(self.Mahler_coefs)

	def __add__(self,right):
		temp = cont_fcn_on_Zp_to_Lambda(0,0,0,[0])
		C = type(self)
		if C !=	type(temp):
			return C(self.p,self.base_ring,self.Mahler_coefs+right.Mahler_coefs)
		else:
			return C(self.p,self.comp,self.base_ring,self.Mahler_coefs+right.Mahler_coefs)

	def scale(self,left):
		temp = cont_fcn_on_Zp_to_Lambda(0,0,0,[0])
		C = type(self)
		if C !=	type(temp):
			return C(self.p,self.base_ring,left*self.Mahler_coefs)
		else:
			return C(self.p,self.comp,self.base_ring,left*self.Mahler_coefs)

	def __sub__(self,right):
		return self+right.scale(-1)

	def __cmp__(self,right):
		return cmp((self.p,self.base_ring,self.Mahler_coefs),(right.p,right.base_ring,right.Mahler_coefs))

	def zero(self):
		temp = cont_fcn_on_Zp_to_Lambda(0,0,0,[0])
		C = type(self)
		if C !=	type(temp):
			return C(self.p,self.base_ring,vector([self.base_ring(0) for i in range(0,self.num_coefs())]))
		else:
			return C(self.p,self.comp,self.base_ring,vector([self.base_ring(0) for i in range(0,self.num_coefs())]))

    ## This function forms Delta^(-1) of self by shifting all of the moments to the right and inserting 0 as the 0-th moment
	def solve_diff_eqn(self):
		print "Warning: Solving difference equation with constant term",self.Mahler_coef(0)
		w = seq(self.Mahler_coefs)
		w.reverse()
		w.pop()
		w.reverse()		
		w = w + [0]
		temp = cont_fcn_on_Zp_to_Lambda(0,0,0,[0])
		C = type(self)
		if C !=	type(temp):
			return C(self.p,self.base_ring,vector(w))
		else:
			return C(self.p,self.comp,self.base_ring,vector(w))

    ## Need to figure this out eventually
	def normalize(self):
		return self



		


class cont_fcn_on_Zp_to_Lambda(cont_fcn_on_Zp):
	def __init__(self,p,r,Lambda,coefs):
		cont_fcn_on_Zp.__init__(self,p,Lambda,coefs)
		self.comp = r

#  def act_left(self,gamma):
#      new_coefs = form_acting_matrix_on_Lambda_valued_fcns(self,gamma)*self.Mahler_coefs.column()

#      return cont_fcn_on_Zp_to_Lambda(self.p,self.comp,self.base_ring,new_coefs.list())

	def act_right(self,gamma):
		new_coefs = self.Mahler_coefs * form_acting_matrix_on_Lambda_valued_fcns(self,gamma)
		
		return cont_fcn_on_Zp_to_Lambda(self.p,self.comp,self.base_ring,new_coefs.list())

#      return self.act_left(gamma.adjoint())

	def valuation(self):
		return min([power_of_maxl_ideal(self.Mahler_coef(a)) for a in range(self.num_coefs())])

	def specialize(self,k):
		v=[]
		eval = (1+p)^k-1
		for c in self.Mahler_coefs:
			f=c.polynomial()
		if f!=0:
			ans=f.substitute(eval)
		else:
			ans=0
		v+=[ans]

		return cont_fcn_on_Zp(self.p,self.base_ring.base_ring(),v)

	  


def form_acting_matrix_on_Lambda_valued_fcns(f,gam):
	##only coded for characteristic p
	a=gam[0,0]
	b=gam[0,1]
	c=gam[1,0]
	d=gam[1,1]
	p=f.p
	assert f.base_ring.base_ring() == GF(p)
	s = f.num_coefs()
	Lambda = f.base_ring
	if Lambda.base_ring() != GF(p):
		M = Lambda.base_ring().precision_cap()
	T = Lambda.gens()[0]

	answer = [[Lambda(0) for i in range(s)] for i in range(s)]

	if Lambda.base_ring() != GF(p):
		wd = teich(d,p,M)
	else:
		wd = GF(p)(d)

	logpgam = ZZ(logp_fcn(p,10*s,1+p))  #accuracy total ad hoc here

	v1 = [(ZZ(logp_fcn(p,10*s,a+c*i)))/logpgam for i in range(0,s)]
	v1 = [sum([GF(p)((binomial(v1[i],q))) * T^q for q in range(Lambda.default_prec()+1)]) for i in range(0,s)]

	##v1[i] should now be [a+c*i] as a power series in T

	for n in range(0,s):
		for m in range(0,s):
			answer[m][n] = sum([(-1)^(m-i)*GF(p)(binomial(m,i))*GF(p)(binomial((b+d*i)/(a+c*i),n))*(v1[i]) for i in range(0,m+1)])

#    logpgam = logp_fcn(p,10*s,1+p)  #accuracy total ad hoc here
#    v1 = [logp_fcn(p,10*s,a+c*i)/logpgam for i in range(0,s)]
#    for n in range(0,s):	   
#    	vtemp = [(b+d*i)/(a+c*i) for i in range(0,s)] 
#        v2 = [binomial((b+d*i)/(a+c*i),n) for i in range(0,s)]
#	for m in range(0,Lambda.default_prec()+1):
#	    v3 = [binomial(v1[i],m)*v2[i] for i in range(0,s)]
#	    for j in range(s):
#	    	cc = sum([(-1)^(j-i)*binomial(j,i)*v3[i] for i in range(j+1)])
#	    	answer[j][n] += T^m * Lambda.base_ring()(cc) + O(T^Lambda.default_prec()+1)

	return Matrix(answer)*(wd^f.comp)
	    	
   

def power_of_maxl_ideal(f):
	R=f.parent().base_ring()
	p=R.base_ring().prime()
	T=R.gens()[0]
	v=f.padded_list()
	return min([v[a].valuation()+a for a in range(len(v))])


	

