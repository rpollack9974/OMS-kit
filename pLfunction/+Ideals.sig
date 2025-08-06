175,0
V,montestalk,4
A,FldNum,9,pBasis,Discriminant,FactorizedDiscriminant,FactorizedPrimes,IntegralBasis,LocalIndex,pHermiteBasis,PrimeIdeals,TreesIntervals
S,CompensateValue,"tree is an interval [i..j] inside [1..#K`PrimeIdeals[p]] and exponents is a sequence of integers of length #tree. The output is a power of the greatest common phi-polynomial of the tree, such that v_P >= exponents[P] for all P in the tree",0,5,0,0,1,0,0,1,1,-38,,0,0,-1,,0,0,-1,,0,0,-1,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,Construct,"This routine constructs a polynomial Ppol with integer coefficients such that: deg Ppol<m_i+1 and y^nu*R_i(Ppol)(y)=respol(y), where nu=ord_y(respol). The non-negative integers s,u are the coordinates of the left endpoint of a segment of slope -type[i]`slope supporting N_i(Ppol)",0,6,0,0,1,0,0,1,1,-38,,0,0,-1,,0,0,-1,,0,0,-1,,1,1,-38,,0,0,-1,,-38,-38,-38,-38,-38,-38
S,ConvertLogs,"The class mod P of the product of p^log[1]·Phi_1^log[2]···Phi_i^log[i+1], where P is the prime ideal given by type",0,3,0,0,1,0,0,1,1,-38,,0,0,-1,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,CrossedValues,Compute the values of the attribue P`CrossedValues for all prime ideals P in K`PrimeIdeals[p],0,2,0,0,1,0,0,0,0,-1,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,CRT,Compute x congruent to elements[j] mod ideals[j] for every j. Integrality of the given elements is not checked!,2,0,1,82,0,28,1,1,82,0,270,2,0,0,0,0,0,0,0,82,,0,0,82,,28,-38,-38,-38,-38,-38
S,Different,Valuation of the different ideal of the local extension of Qp given by the p-adically irreducible polynomial represented by the given type,0,2,0,0,1,0,0,1,1,-38,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,EqualizeLogs,Add zeros to the shorter first list to achieve the same length as the second list,0,2,0,0,1,0,0,1,1,-38,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,GCPhi,The routine stores in phi the greatest common phi-polynomial of the tree. Values is the sequence of all v_P(phi(theta)) for P in the tree. node is the level of phi,0,6,0,0,1,0,0,1,1,-38,,1,1,-38,,1,1,-38,,0,0,-1,,0,0,-1,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,Generators,Compute the generators of the prime ideals in K above the rational prime p,0,2,0,0,1,0,0,0,0,-1,,0,0,-1,,-38,-38,-38,-38,-38,-38
S,IndexOfCoincidence,"The index is 0 if t1,t2 belong to different trees. Otherwise, it is the least index such that the triplets (t1[i]`Phi,t1[i]`slope,t1[i]`psi) and (t2[i]`Phi,t2[i]`slope,t2[i]`psi) are different. The types must correspond to different prime ideals",0,3,0,0,1,0,0,1,1,-38,,1,1,-38,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,InitialLevel,Initialize a typelevel record with the given data. psi is a monic irreducible factor of Pol modulo p and power=ord_psi(Pol mod p),0,4,0,0,0,0,0,0,0,-1,,0,0,-1,,0,0,-1,,0,0,-1,,270,-38,-38,-38,-38,-38
S,IntegralBasis,Compute a basis of the maximal order ZK of K and the discriminant of K,0,1,0,0,0,0,0,0,0,27,,82,-38,-38,-38,-38,-38
S,Inversionloop,Apply one iteration of the classical p-adic Newton method to find and approximation xnum/xden to the inverse of A,0,6,0,0,1,0,0,0,0,-1,,0,0,-1,,0,0,-1,,1,1,-38,,1,1,-38,,0,0,-1,,-38,-38,-38,-38,-38,-38
S,IsIntegralM,True iff the algebraic number alpha is integral. It should be fasther than the Magma standard routine,0,1,0,0,0,0,0,0,0,28,,36,-38,-38,-38,-38,-38
S,LastLevel,Technical routine for the final part of the Montes algorithm,0,4,0,0,1,0,0,0,0,-1,,0,0,-1,,1,1,-38,,0,0,-1,,-38,-38,-38,-38,-38,-38
S,Lift,,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,28,-38,-38,-38,-38,-38
S,Lift,,0,3,0,0,0,0,0,0,0,-1,,0,0,-1,,0,0,-1,,28,-38,-38,-38,-38,-38
S,LocalCRT,,0,4,0,0,1,0,0,1,1,-38,,0,0,-1,,0,0,-1,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,MultipliersGenerators,,0,3,0,0,1,0,0,1,1,-38,,0,0,-1,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,Localize,"output=den,exp,Pol such that alpha = (1/den)*Pol(theta)*p^exp, and den is coprime to p",0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,148,148,312,-38,-38,-38
S,LocalLift,"class should belong to the residue class field type[r]`Fq. The output is a pair g,e such that g(theta)/p^e is a lift to a P-integral element in K and deg g(x)<n_P",0,4,0,0,1,0,0,1,1,-38,,1,1,-38,,0,0,-1,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,LocalLift,class should belong to the residue class field Z_K/P. The output is a lift to a P-integral element in K,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,28,-38,-38,-38,-38,-38
S,LocalLift,,0,3,0,0,0,0,0,0,0,-1,,0,0,-1,,0,0,-1,,28,-38,-38,-38,-38,-38
S,Montes,Apply the Montes algorithm to the number field K and the rational prime p. The option Basis:=True forces the computation of a p-integral basis of K,0,2,0,0,1,0,0,0,0,148,,0,0,27,,-38,-38,-38,-38,-38,-38
S,Montesloop,Perform the main loop of the Montes algorithm with the given data,0,5,0,0,1,0,0,1,1,-38,,1,1,-38,,1,1,-38,,1,1,-38,,0,0,-1,,-38,-38,-38,-38,-38,-38
S,MontesloopFactors,Modified main loop of the Montes algorithm used in the factorization routines. The iteration stops as soon as totalindex is greater than the given mahler bound,0,4,0,0,1,0,0,0,0,-1,,1,1,-38,,1,1,-38,,0,0,-1,,-38,-38,-38,-38,-38,-38
S,Multiplier,"Compute an element mult in the number field Parent(P) which is congruent to 1 modulo P^a_P and it has Q-value >= a_Q. The output has a power of p as denominator; thus, if all a_Q>=0, the output is an algebraic integer",0,3,0,0,1,0,0,1,1,-38,,0,0,-1,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,MultiplyByInverse,"Divide alpha by a pseudo-inverse, so that after the routine, it is congruent to 1 modulo P^m",0,3,0,0,1,0,0,0,0,-1,,1,1,-38,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,MultPiece,"Compute bp in Parent(P) which has P-value zero and v_Q(bp) >= expsTree[Q]+extraden*e_Q, for all Qne P in the tree",0,5,0,0,1,0,0,1,1,-38,,1,1,-38,,0,0,-1,,0,0,-1,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,Newton,"Given a type of order at least i, and the phiadic expansion of a polynomial, compute: - sides=list of sides of the r-th order Newton polygon w.r.t. the type; - devsEachSide[k]=list of multiadic phi_1,...,phi_i-1 expansion of the coefficients of the polynomial whose attached point lies on sides[k]",0,5,0,0,1,0,0,1,1,-38,,1,1,-38,,1,1,-38,,1,1,-38,,0,0,-1,,-38,-38,-38,-38,-38,-38
S,pDiscriminant,"Compute: -pdiscK: sum of the p-adic valuations of the discriminants of all local extensions of Q_p, given by the irreducible p-adic factors of the given polynomial. -pdiscf: is the p-adic valuation of the discriminant of polynomial. Note that the discriminant itself is not computed",0,2,0,0,0,0,0,0,0,312,,0,0,148,,148,148,-38,-38,-38,-38
S,pFactors,"Compute: - list: a list of Okutsu approximations to the irreducible p-adic factors of the given polynomial, all of them correct modulo p^precision. - OMReps: a list of OM representations of the irreducible factors of polynomial. -totalindex: p-index of polynomial",0,3,0,0,0,0,0,0,0,148,,0,0,312,,0,0,148,,82,82,148,-38,-38,-38
S,pHermiteBasis,Compute a p-integral basis of ZK in HNF,0,2,0,0,0,0,0,0,0,148,,0,0,27,,82,-38,-38,-38,-38,-38
S,pIntegralBasis,Compute a p-integral basis of ZK,0,2,0,0,0,0,0,0,0,148,,0,0,27,,82,-38,-38,-38,-38,-38
S,PrescribedValue,"Compute a polynomial Phi=phi_1^a_1...phi_r^a_r such that v_P(p^a_0Psi(theta))=value, where P is the prime determined by the given type with Okutsu depth r. The exponents a_0,...,a_r are stored in the list logphi",0,4,0,0,1,0,0,1,1,-38,,1,1,-38,,0,0,-1,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,pResultant,Compute the p-adic valuation of the resultant of the two given univariate polynomials. Note that the resultant itself is not computed,0,3,0,0,0,0,0,0,0,312,,0,0,312,,0,0,148,,148,-38,-38,-38,-38,-38
S,PValuation,"Compute the P-valuation v of alpha at the prime ideal P. If the option RED is set to true, compute also the class of alpha in P^v/P^(v+1)",0,2,0,0,0,0,0,0,0,270,,0,0,267,,148,85,-38,-38,-38,-38
S,PValuation,"Compute the P-valuation v of alpha at the prime ideal P. If the option RED is set to true, compute also the class of alpha in P^v/P^(v+1)",0,2,0,0,0,0,0,0,0,270,,0,0,148,,148,85,-38,-38,-38,-38
S,PValuation,"Compute the P-valuation v of alpha at the prime ideal P. If the option RED is set to true, compute also the class of alpha in P^v/P^(v+1)",0,2,0,0,0,0,0,0,0,270,,0,0,28,,148,85,-38,-38,-38,-38
S,Cancel,"Cancell the powers of p in the numerator and denominator of the fraction poly/p^vden, returning a polynomial outpoly and an exponent outputvden such that outpoly/p^outvden=poly/p^vden",0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,312,148,-38,-38,-38,-38
S,mod,Compute the reduction map ZK--> ZK/P,0,2,0,0,0,0,0,0,0,270,,0,0,28,,85,-38,-38,-38,-38,-38
S,Reduction,Compute the reduction map ZK--> ZK/P,0,2,0,0,0,0,0,0,0,270,,0,0,28,,85,-38,-38,-38,-38,-38
S,Reduction,Compute the reduction map ZK--> ZK/P^m,0,3,0,0,0,0,0,0,0,148,,0,0,270,,0,0,28,,82,-38,-38,-38,-38,-38
S,Representative,Construction of a representative phi of a type. We add phi and V at a new level of type,0,1,0,0,1,0,0,1,1,-38,,-38,-38,-38,-38,-38,-38
S,ResidualPolynomial,Internal procedure to compute the i-th residual polynomial psi with respect to a side S of slope -type[i]`slope of the Newton polygon of a certain polynomial Pol. The coefficients of Pol whose attached points in N_i(Pol) lie on S have multiadic expansions contained in the list devsSide,0,4,0,0,1,0,0,1,1,-38,,1,1,-38,,1,1,-38,,0,0,-1,,-38,-38,-38,-38,-38,-38
S,SFL,in type[1]`sfl and type[1]`Phiadic we stored relevant data. The aim is type[#type]`slope>=slope,0,2,0,0,1,0,0,0,0,148,,1,1,82,,-38,-38,-38,-38,-38,-38
S,SFL,"Given a prime ideal P in the number field K, improve its Okutsu approximation phi_(r+1) till P`Type[r+1]`slope> slope. The last level of P`Type is updated with data of the new Okutsu approximation",0,3,0,0,1,0,0,0,0,148,,1,1,270,,1,1,27,,-38,-38,-38,-38,-38,-38
S,SFLInitialize,"Initialize certain values of the given type, which are necessary for the SFL routine",0,1,0,0,1,0,0,1,1,-38,,-38,-38,-38,-38,-38,-38
S,Shrink,"Replace beta by an element num/p^power congruent to beta mod P^m such that num is given by a polynomial of degree < e_Pf_P, The element beta is assumed (without checking) to be P-integral",0,3,0,0,1,0,0,0,0,-1,,1,1,-38,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,SIntegralBasis,Compute a local integral basis for the given set of primes,0,2,0,0,0,0,0,0,0,82,,0,0,27,,82,-38,-38,-38,-38,-38
S,Taylor,Compute the first omega+1 coefficients of the phi-expansion of pol,0,3,0,0,0,0,0,0,0,148,,0,0,312,,0,0,312,,82,-38,-38,-38,-38,-38
S,TreeInterval,Returns the interval of positions in K`PrimeIdeals[p] of the tree to which O belongs,0,2,0,0,1,0,0,1,1,-38,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,TrueDiscriminant,Compute the discriminant (and its factorization) of the maximal order ZK of K,0,1,0,0,0,0,0,0,0,27,,148,82,-38,-38,-38,-38
S,UpdateLastLevel,"Update the values of slope, h, psi and logGamma in the last level of the given type",0,1,0,0,1,0,0,1,1,-38,,-38,-38,-38,-38,-38,-38
S,Value,"Given a level i, a type and a polynomial pol, compute: - devs=multiexpansion with respect to phi_1,...,phi_i-1 of the points in S_lambda_i-1(pol); - val=i-th valuation of pol with respect to type",0,5,0,0,1,0,0,1,1,-38,,1,1,-38,,1,1,-38,,1,1,-38,,0,0,-1,,-38,-38,-38,-38,-38,-38
S,VValuation,,0,2,0,0,0,0,0,0,0,312,,0,0,312,,148,-38,-38,-38,-38,-38
S,Z,The primitive element z_i of the i-th residual finite field F_(i+1) of the type is stored in the variable z,0,3,0,0,1,0,0,1,1,-38,,0,0,-1,,1,1,-38,,-38,-38,-38,-38,-38,-38
S,RationalDenominator,The least positive integer a such that aI is included in the maximal order O,0,1,0,0,0,0,0,0,0,-1,,148,-38,-38,-38,-38,-38
S,TwoElement,Compute a pair of elements generating the ideal I,0,1,0,0,0,0,0,0,0,270,,82,-38,-38,-38,-38,-38
S,TwoElement,Compute a pair of elements generating the ideal,0,1,0,0,1,0,0,1,1,270,,-38,-38,-38,-38,-38,-38
S,IsIdealRecord,True iff I is a record of type IdealRecord,0,1,0,0,0,0,0,0,0,270,,36,-38,-38,-38,-38,-38
S,IsPrimeIdeal,True iff I is a record of type IdealRecord corresponding to a prime ideal,0,1,0,0,0,0,0,0,0,270,,36,-38,-38,-38,-38,-38
S,*,"Compute the product of the fractional ideals I,J. They are both factored if their factorization is not yet known",0,2,0,0,0,0,0,0,0,270,,0,0,270,,270,-38,-38,-38,-38,-38
S,^,Compute the n-th power of the fractional ideal I. The ideal I is factored if its factorization is not known,0,2,0,0,0,0,0,0,0,148,,0,0,270,,270,-38,-38,-38,-38,-38
S,/,"Compute the quotient of the fractional ideals I,J. They are both factored if their factorization is not knwon",0,2,0,0,0,0,0,0,0,270,,0,0,270,,270,-38,-38,-38,-38,-38
S,IsIntegral,True iff I is an integral ideal. The ideal is factored if its factorization is not known,0,1,0,0,0,0,0,0,0,270,,36,-38,-38,-38,-38,-38
S,IsOne,True iff I is the zero ideal,0,1,0,0,0,0,0,0,0,270,,36,-38,-38,-38,-38,-38
S,IsZero,true iff I is the zero ideal,0,1,0,0,0,0,0,0,0,270,,36,-38,-38,-38,-38,-38
S,eq,"True iff the fractional ideals I,J are equal. They are both factored if their factorization is not kwown",0,2,0,0,0,0,0,0,0,270,,0,0,270,,36,-38,-38,-38,-38,-38
S,subset,"True iff the fractional ideal J divides I, i.e., iff I/J is integral. Both ideals are factored if their factorization is not yet known",0,2,0,0,0,0,0,0,0,270,,0,0,270,,36,-38,-38,-38,-38,-38
S,Norm,Compute the norm of the ideal I,0,1,0,0,0,0,0,0,0,270,,148,-38,-38,-38,-38,-38
S,RationalRadical,Compute the rational prime numbers dividing the norm of the ideal I,0,1,0,0,0,0,0,0,0,270,,82,-38,-38,-38,-38,-38
S,+,"Compute the greatest common divisor of the fractional ideals I,J",0,2,0,0,0,0,0,0,0,270,,0,0,270,,270,-38,-38,-38,-38,-38
S,ideal,Define the fractional ideal generated by the elements of listgen,1,1,1,82,0,28,2,0,0,0,0,0,0,0,82,,0,0,27,,270,-38,-38,-38,-38,-38
S,ideal,Define the principal fractional ideal generated by a,0,2,0,0,0,0,0,0,0,28,,0,0,27,,270,-38,-38,-38,-38,-38
S,ideal,Define the principal fractional ideal generated by the integer a,0,2,0,0,0,0,0,0,0,148,,0,0,27,,270,-38,-38,-38,-38,-38
S,Factorization,Compute the decomposition of the fractional ideal I into prime ideals,0,1,0,0,0,0,0,0,0,270,,82,-38,-38,-38,-38,-38
S,Factorization,Compute the decomposition of the fractional ideal I into prime ideals,0,1,0,0,1,0,0,1,1,270,,-38,-38,-38,-38,-38,-38
S,FactorListToString,Write down a factorization in pretty form,0,1,0,0,0,0,0,0,0,-1,,298,-38,-38,-38,-38,-38
S,ResidueField,"Given a prime ideal P, return the residue field Z_K/P",0,1,0,0,0,0,0,0,0,270,,84,-38,-38,-38,-38,-38
S,InitializeType,"Initializa a typelevel record with the given data, and set two lists z, Y to store the primitive elements of the residual fields and the variables of the polynomial rings over these fields",0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,82,82,82,-38,-38,-38
S,EnlargeType,"Enlarge the given type t (and the lists Y, z) with the slope -h/e and residual polynomial psi",0,6,0,0,1,0,0,1,1,-38,,1,1,-38,,1,1,-38,,0,0,-1,,0,0,-1,,0,0,-1,,-38,-38,-38,-38,-38,-38
S,CreateType,"Create a random type t whose invariants [h1,e1,f1,...,hr,er,fr] are specified in the list ll",0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,82,-38,-38,-38,-38,-38
S,CreateRandomType,Create a random type of order r,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,82,-38,-38,-38,-38,-38
S,RandomMultiplicityType,"Creates a random type of depth r and randomly combines s of its phi-polynomials, adding some random refinements. The full type is always included",0,3,0,0,0,0,0,0,0,-1,,0,0,-1,,0,0,-1,,312,-38,-38,-38,-38,-38
S,CreateRandomMultipleTypePolynomial,Compute a random irreducible polynomial with k types of order AT MOST r. The value of s is used to add a power of p to ensure irreducibility,0,4,0,0,0,0,0,0,0,-1,,0,0,-1,,0,0,-1,,0,0,-1,,312,-38,-38,-38,-38,-38
S,CombineTypes,Compute and irreducible polynomial whose attached types are the given ones in the specified list,0,1,0,0,0,0,0,0,0,82,,312,-38,-38,-38,-38,-38
S,CombinePolynomialsWithDifferentPrimes,"Compute a polynomial which is congruent to the given polynomials f1, f2 modulo the specified powers of the primes p1, p2",0,5,0,0,0,0,0,0,0,-1,,0,0,-1,,0,0,-1,,0,0,-1,,0,0,-1,,312,-38,-38,-38,-38,-38
S,GlobalExpansion,Compute the coefficients of the multi-phi-adic expansion of pol. They are stored in a recursive list,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,168,-38,-38,-38,-38,-38
S,Expand,This function is only useful to check the validity of expansions given by GlobalExpand,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,312,-38,-38,-38,-38,-38
S,ExpandTeX,Write in TeX form the multi-phi-adic expansion of pol,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,-54,-38,-38,-38,-38,-38
S,ExpandTeXAux,,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,-54,-38,-38,-38,-38,-38
S,ExpandPhiTeX,Write the phi-adic expansion of phi_k in TeX format,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,-54,-38,-38,-38,-38,-38
S,ExpandAllPhiTeX,Write in TeX format the phi-adic expansion of all the phi in the type,0,1,0,0,0,0,0,0,0,-1,,-54,-38,-38,-38,-38,-38
S,ExpandMagma,Write in Magma form the multi-phi-adic expansion of pol,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,-54,-38,-38,-38,-38,-38
S,ExpandMagmaAux,,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,-54,-38,-38,-38,-38,-38
S,ExpandPhiMagma,Write the phi-adic expansion of phi_k in Magma format,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,-54,-38,-38,-38,-38,-38
S,ExpandAllPhiMagma,Write in Magma format the phi-adic expansion of all the phi in the type,0,1,0,0,0,0,0,0,0,-1,,-54,-38,-38,-38,-38,-38
