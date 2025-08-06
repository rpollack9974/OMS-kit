from sage.structure.sage_object import SageObject

#################################################################################################################
##  A continuous function f:Z_p-->R with R a p-adic ring has a Mahler expansion f = sum_n a_n (x choose n) 
##  where {a_n} is a sequence in R converging to 0.  We represent such a function by the sequence {a_n} (or
##  at least some approximation of this sequence to be determined later).
#################################################################################################################

class measure_on_Zp(SageObject):
	def __init__(self,p,R,moments,k=None,comp=None):
		"""
		Initializes the R-valued function 

		INPUT:
			- p -- prime number
			- R -- p-adic ring where the functions take value
			- Mahler_coefs -- a vector of elements of R which represents the Mahler coefficients
			- k -- weight by which matrices act (could be None)
			- comp -- component of weight space where action occurs (could be None)

		OUTPUT:

		A measure whose value on (x choose n) is moment[n].	
		"""
		self.p=p
		self.base_ring = R
		moments = [R(moments[a]) for a in range(len(moments))]
		self.comp=comp
		self.k = k 
		self.Mahler_coefs = vector(moments)

	def __repr__(self):
		return repr(self.Mahler_coefs)

	def Mahler_coef(self,n):
		return self.Mahler_coefs[n]

	def num_coefs(self):
		return len(self.Mahler_coefs)

	def __add__(self,right):
		return measure_on_Zp(self.p,self.base_ring,self.Mahler_coefs+right.Mahler_coefs,k=self.k,comp=self.comp)

	def scale(self,left):
		return measure_on_Zp(self.p,self.base_ring,left*self.Mahler_coefs,k=self.k,comp=self.comp)

	def __sub__(self,right):
		return self+right.scale(-1)

	def __cmp__(self,right):
		return cmp((self.p,self.base_ring,self.Mahler_coefs,self.k,self.comp),(right.p,right.base_ring,right.Mahler_coefs,right.k,right.comp))

	def zero(self):
		v = vector([self.base_ring(0) for i in range(0,self.num_coefs())])
		return measure_on_Zp(self.p,self.base_ring,v,k=self.k,comp=self.comp)

    ## This function forms Delta^(-1) of self by shifting all of the moments to the right and inserting 0 as the 0-th moment
	def solve_diff_eqn(self):
		print "Warning: Solving difference equation with constant term",self.Mahler_coef(0)
		w = seq(self.Mahler_coefs)
		w.reverse()
		w.pop()
		w.reverse()		
		w = w + [0]
		return measure_on_Zp(self.p,self.base_ring,vector(w),k=self.k,comp=self.comp)

    ## Need to figure this out eventually
	def normalize(self):
		M = self.num_coefs()
		p = self.p
		if type(self.k)==type(1):
			for j in range(M):
				self.Mahler_coefs[j] = self.Mahler_coefs[j] % (p^(M-j))
		else:
			w = self.base_ring.gen()
			for j in range(M):
				self.Mahler_coefs[j] = self.Mahler_coefs[j].truncate(M-j)
		return self

	def act_right(self,gamma):
		a = gamma[0,0]
		b = gamma[0,1]
		c = gamma[1,0]
		d = gamma[1,1]
		if type(self.k) == type(1):
			new_coefs = self.Mahler_coefs * form_acting_matrix_in_fixed_weight(self.p,self.k,self.num_coefs(),a,b,c,d)
		elif self.comp != None:
			new_coefs = self.Mahler_coefs * form_acting_matrix_on_rim(self.p,self.comp,self.num_coefs(),a,b,c,d)
		else:
			print "Yikes"
			
		return measure_on_Zp(self.p,self.base_ring,new_coefs.list(),k=self.k,comp=self.comp).normalize()

#      return self.act_left(gamma.adjoint())

	def valuation(self):
		return min([self.Mahler_coef(a).valuation() for a in range(self.num_coefs())])

	def decrease_accuracy(self,M):
		self.Mahler_coefs = self.Mahler_coefs[0:M]
		self = self.normalize()

	def measure_to_distribution(self):
		C = poly_to_binom(self.num_coefs())
		data = self.Mahler_coefs * C
		return dist(self.p,self.k,data)

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

@cached_function
def B(a,b):
	return binomial(a,b)


@cached_function
def Bp(a,b,p):
	return binomial(a,b)%p

@cached_function
def poly_to_binom(M):
	R.<z>=PolynomialRing(QQ)
	ans = []
	for j in range(M):
		v = binomial(z,j).padded_list()
		while len(v) < M:
			v += [0]
		ans += [v]
	return (Matrix(ans).transpose())^(-1)


@cached_function
def form_acting_matrix_in_fixed_weight(p,k,s,a,b,c,d):
#	a = gam[0,0]
#	b = gam[0,1]
#	c = gam[1,0]
#	d = gam[1,1]
#	p = mu.p
#	s = mu.num_coefs()
#	R = mu.base_ring

	answer = [[0 for i in range(s)] for i in range(s)]

#	logpgam = ZZ(logp_fcn(p,10*s,1+p))  #accuracy total ad hoc here

#	v1 = [(ZZ(logp_fcn(p,10*s,a+c*i)))/logpgam for i in range(0,s)]
#	v1 = [sum([(binomial(v1[i],q)) * T^q for q in range(Lambda.default_prec()+1)]) for i in range(0,s)]

	v1 = [(a+c*i)^k for i in range(0,s)]
	##v1[i] should now be [a+c*i] as a power series in T

	for n in range(0,s):
		for m in range(0,s):
			answer[m][n] = sum([(-1)^(m-i)*(B(m,i))*(B((b+d*i)/(a+c*i),n))*(v1[i]) for i in range(0,m+1)]) % (p^s)

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

	return Matrix(answer)

@cached_function
def form_acting_matrix_on_rim(p,comp,s,a,b,c,d):
	answer = [[0 for i in range(s)] for i in range(s)]

	logpgam = ZZ(logp_fcn(p,10*s,1+p))  #accuracy total ad hoc here

	Lambda.<w> = PowerSeriesRing(GF(p),s)
	w = Lambda.gen()
	v1 = [(ZZ(logp_fcn(p,10*s,a+c*i)))/logpgam for i in range(0,s)]
	v1 = [sum([(GF(p)(binomial(v1[i],q))) * w^q for q in range(Lambda.default_prec()+1)]) for i in range(0,s)]
	##v1[i] should now be [a+c*i] as a power series in w

	for n in range(0,s):
		for m in range(0,s):
			answer[m][n] = sum([(-1)^(m-i)*(Bp(m,i,p))*(Bp((b+d*i)/(a+c*i),n,p))*(v1[i]) for i in range(0,m+1)]) 


	return Matrix(answer)*(GF(p)(d))^comp


	  	

	  


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


	

def teich(a,p,M):
	R=pAdicField(p,M)
	return ZZ(R.teichmuller(a))
