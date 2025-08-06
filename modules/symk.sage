import sage.rings.polynomial.multi_polynomial_element as MPol
from sage.structure.sage_object import SageObject

class symk(SageObject):
	def __init__(self,k,poly=None,chi=trivial_character(1),base_ring=QQ):
		"""A symk object is stored as a homogeneous polynomial of degree k

Inputs: 
	k -- weight 
	chi -- Dirichlet character 
	poly -- homogeneous of weight k in X and Y
	base_ring -- ring containing the coefficients of poly"""

		#assert (poly == None) or (poly == 0) or (k==0) or (poly.is_homogeneous()), "must enter a homogeneous polynomial"
		#if (poly != None) and (poly !=0) and (k<>0):
		#	assert poly.total_degree() == k, "the weight is incorrect"
		if poly != None:
			self.poly=poly
		else:
			R.<X,Y>=PolynomialRing(base_ring,2)
			self.poly=0*X
		self.weight=k
		self.base_ring=base_ring
		self.chi=chi
			
	def __repr__(self):
		return repr(self.poly)

	def coef(self,j):
		"""returns coefficient of X^j*Y^(k-j)"""
		v=self.vars()
		X=v[0]
		Y=v[1]
		k=self.weight

		return self.poly[j,k-j]

	def __add__(self,right):
		"""returns self+right"""
		#assert self.weight == right.weight, "weights are unequal"
		return symk(self.weight,chi=self.chi,poly=self.poly+right.poly)

	def scale(self,left):
		"""returns left*self"""
		if self.is_zero():
			return self
		else:
			return symk(self.weight,chi=self.chi,poly=left*self.poly)

	def __sub__(self,right):
		"""returns self-right"""
		#assert self.weight == right.weight, "weights are unequal"
		return self+right.scale(-1)	

	def __cmp__(self,right):
		return cmp((self.weight,self.chi,self.poly),(right.weight,right.chi,right.poly))

	def zero(self):
		return symk(self.weight,chi=self.chi)

	def vars(self):
		"""Returns the variables defining Sym^k"""
		return self.poly.parent().gens()		

	def base_ring(self):
		return self.base_ring

	def is_zero(self):
		ans = True
		j = 0
		while ans and j<=self.weight:
			ans = self.coef(j) == 0
			j = j + 1
		return ans

#remove_binom here is changing the integral lattice depending on whether we are using
#V_k or P_k^*
	def valuation(self,w,remove_binom=false):
		"""returns the exponent of the highest power of p which divides all coefficients of self"""
		k=self.weight
		v=self.vars()
		X=v[0]
		Y=v[1]
		v=[]
		if type(w) == sage.rings.integer.Integer:
			w = QQ.valuation(w)
		for j in range(k+1):
			if not remove_binom:
				v=v+[w(self.poly.monomial_coefficient(X^j*Y^(k-j)))]
			else:
				v=v+[w(self.poly.monomial_coefficient(X^j*Y^(k-j)))-w(binomial(k,j))]

		return min(v)
		

	def filtration(self,p,remove_binom=true):		
		assert self.valuation(p,remove_binom=remove_binom) >= 0,"symk not integral"
		k = self.weight
		filt_level = k 
		for j in range(k+1):
			if type(p) == sage.rings.integer.Integer:
				filt_level = min(filt_level,self.coef(j).valuation(p)+j-binomial(k,j).valuation(p))
			else:
				e = 1/p(p.uniformizer())
				filt_level = min(filt_level,p(self.coef(j))*e+j-p(binomial(k,j))*e)

		return filt_level


	def normalize(self):
		return self

	def map(self,psi):
		"""psi is a map from the base_ring to Qp and this function applies psi to all polynomial coefficients and then lifts them to QQ"""
		#assert psi.domain()==self.base_ring
		k=self.weight
		S.<X,Y>=PolynomialRing(QQ)
			
		ans=0*X
		for j in range(k+1):
			ans=ans+psi(self.coef(j)).lift()*X^j*Y^(k-j)
		temp=copy(self)
		temp.poly=ans
		temp.base_ring=psi.codomain()

		return temp
			
	def map2(self,psi):
		"""simply apply map2 to self"""
		k=self.weight
		S.<X,Y>=PolynomialRing(psi.codomain())
			
		ans=0*X
		for j in range(k+1):
			ans=ans+psi(self.coef(j))*X^j*Y^(k-j)
		temp=copy(self)
		temp.poly=ans
		temp.base_ring=psi.codomain()

		return temp

	def act_right(self,gam):
		"""returns self|gam where (P|[a,b;c,d])(X,Y) = P(dX-cY,-bX+aY)"""
		if self.weight==0:
			if self.chi==None:
				return self
			else:
				return self.scale(self.chi(gam[0,0]))
		else:
			a=gam[0,0]
			b=gam[0,1]
			c=gam[1,0]	
			d=gam[1,1]
			v=self.vars()
			X=v[0]
			Y=v[1]
			## should the action have a chi(a) or a chi(d)??
			if self.chi==None:
				return symk(self.weight,chi=self.chi,poly=self.poly(d*X-c*Y,-b*X+a*Y))			
			else:
				return symk(self.weight,chi=self.chi,poly=self.chi(a)*self.poly(d*X-c*Y,-b*X+a*Y))

	def lift_to_dist(self,p,N):
		"""returns some (p-adic) distribution with N moments which specializes to self"""
		k=self.weight
		#assert N >= k+1, "need more moments"
		if k==0:
			moments=[QQ(self.poly)]
		else:
			v=self.vars()
			X=v[0]
			Y=v[1]
			moments=[]
			for j in range(k+1):
				moments=moments+[QQ(self.poly.coefficient(X^j*Y^(k-j))/(binomial(k,j)*(-1)^j))]
		while len(moments)<N:
			moments=moments+[0]
		moments=moments[0:N]
		mu=dist(p,k,vector(moments),char=self.chi)
#		if mu.valuation()<0:
#			print("scaling by ",p,"^",-mu.valuation()," to keep things integral")
#			mu=mu.scale(p^(-mu.valuation()))
		return mu

	def vector_of_coefs(self):
		return [self.coef(j) for j in range(self.weight+1)]

def matrix_of_gamma_minus_1(k,gam,base_ring=QQ):
	S.<X,Y>=PolynomialRing(base_ring)
	ans = []
	for j in range(0,k+1):
		P = symk(k,X^j*Y^(k-j),base_ring=base_ring)
		Q = P.act_right(gam)-P
		v = Q.vector_of_coefs()
		ans += [v]
	return Matrix(ans)

		
		