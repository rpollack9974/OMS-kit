//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//    Montes Package v3.01
//    J. Guardia, J. Montes, E. Nart 
//    July 2009
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////////////////
// Setembre 09
// Arreglat un bug en els generadors en ordre 0
///////////////////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//
//  Juliol -2009
//  *  El record "primeideal" s'ha modificat: l'entrada "generador" ha passat 
//     de ser un polinomi a ser un element del cos de nombres.
//  *  Eliminat l'us de les bases de Groebner; substituit per HermiteForm
//  *  Dues rutines locals: localmontesmatrix i localmontes
//  *  La rutina global passa de dir-se "MIB" a dir-se "HNIntegralBasis"
//  *  Els generadors dels ideals ja no son polinomis, sino elements del cos de nombres 
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//
//  Maig -2009
//  *  Incorporat el calcul de la base d'enters global
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//
//  Desembre-2008
//  *  Incorporat el calcul de la base d'enters local
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//
//  Novembre-2008
//  *  Modificat el record "type"-> afegida la llista Quot
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//
//  25-7-2008
//  * Arreglat un bug: els DominatedTypes calia afegir-los a la copia ta del tipusactual
//  * Modificat el record "typelevel": eliminats "slope0" i "refina", afegit "DominatedTypes"
//  * Canviat el nom "finaltypes" per COMPLETETYPES
//  * Canviat el calcul de generadors: eliminat CompareTypes
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//
//  20-7-2008
//  * Canviada l'opcio per defecte del calcul de generadors
//  * Canviat l'output dels costats del poligon de Newton
//  * El calcul de generadors s'ha mogut a una funcio independent
//  * Modificades les funcions per escriure desenvolupaments, perque retornin els resultats
//  * Modificades les funcions per construir tipus, perque retornin els resultats
//
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//
//  14-7-2008
//
//  * Reordenats els arguments de la funcio EnlargeType
//  * Modificades les funcions per escriure els resultats
//
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////
//
//  11-7-2008
//
//  * Traslladat el calcul dels inversos de les Phis al final de la funcio MontesAux
//  * Eliminada la dada "InversePhi" dels tipus  
//
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//
//  10-7-2008
//
//  * Arreglat un bug en la funcio ResidualPolynomial, referent a Evaluate una constant
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//
//  2-7-2008
//
//
// Canvis: 
// *) Eliminada tota la part de "Checking" de montesaux
//
// *) Afegits els vprint de l'indexphi
// 
// *) Suprimit el cas k=1 de la funcio Construct 
//
// *) Incorporats els termes aleatoris en ordre 1.
// 
// *) Corregida la funcio EnlargeType
//
// *) Noves funcions GlobalExpansion i Expand
////////////////////////////////////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////
//
//  30-6-2008 
//
// Canvis
// 
//  Corregit el calcul de l'index
//  Corregit un bug (Vphi en minuscula)
/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////

 


declare verbose montestalk, 5;



PrimeIdeal:=recformat<
prime: Integers(),
generator: FldNumElt,
e: Integers(),
f: Integers()
>;



TypeLevel:=recformat<

Prime : Integers(), /* input prime,  only in level 1*/

Pol: RngUPolElt,    /* input polynomial, only in level 1*/


Phi: RngUPolElt,

PhiPowers: SeqEnum,  /* powers of Phi */


d: Integers(),   /* degree of Phi*/

Quotients: SeqEnum,

ProductOfQuotients: SeqEnum,  /* Quotients (only a part) in the Phi-adic expansion of Pol*/

ProductOfQuotientsValuations: SeqEnum, /* Coordinates of the end point of the side in every order */

h: Integers(),

e: Integers(),


DominatedTypes,  /* posicio (en COMPLETETYPES) i pendent dels tipus que seran influenciats */

slope: Rationals(),

f: Integers(),

psi: RngUPolElt,

Fq: FldFin,

FqY:RngUPol,

z: FldFinElt,

VPhi: Integers(),

b: Integers(),

Phiadic: SeqEnum,

cuttingslope: Integers()
>;


intrinsic HNIntegralBasis(Pol::RngUPolElt,primelist::SeqEnum:  Generators:=false, Diag:="Integers" )->SeqEnum,SeqEnum
{   }
Zx:=Parent(Pol);
x:=Zx.1;
N:=Degree(Pol);
basisnumlist:=[];
basisdenlist:=[];
indexlist:=[];
idealslist:=[];
trueprimelist:=[];
for p in primelist do
    ind,basenums,basedenoms,ids:=localmontesmatrix(Pol,p: generadors:=Generators, diag:=Diag);
	Append(~indexlist,[p,ind]);
	Append(~idealslist,[*p,ids*]);
    
    if ind gt 0 then
		Append(~trueprimelist,p);
		Append(~basisnumlist,basenums);
		Append(~basisdenlist,basedenoms);
	end if;
end for;


K:=NumberField(Pol: Check:=false, Global:=true);

GLOBALBASIS:=[ K!1];

//print "trueprimelist:=",trueprimelist;

if #trueprimelist eq 0 then
 
    GLOBALBASIS:=[ K.1^k: k in [0..N-1]];   
else
    for i:=N-1 to 1 by -1 do
	    MM:=[basisdenlist[k,i]   : k in [1..#trueprimelist] ];
        coeffs:=[];
	    for j:=i+1 to N do 
           XX:=[basisnumlist[k,i,j]   : k in [1..#trueprimelist] ]; 
           Append(~coeffs, CRT(XX,MM));
    	end for;
        coeffs:=Reverse(coeffs) cat [0: j in [1..N-#coeffs] ];
        Append(~GLOBALBASIS,(K.1^(N-i)+K!coeffs)/&*MM );
    end for;
    
end if;    


return GLOBALBASIS,indexlist,idealslist;

end intrinsic;



  

intrinsic montesaux(~StackTipus, ~idealfactors, ~indextotal, ~Basis,~BasisValuations: 
        generators:=false )
{}
COMPLETETYPES:=[];
indextotal:=0;
temps1:=Cputime();
while(#StackTipus gt 0) do   // GRAN WHILE
    vprint montestalk,2:  "++++++++++++++++++++++++++++++++++++++++++++++++";
    vprint montestalk,2:  "++++++++++++++++++++++++++++++++++++++++++++++++";
    vprint montestalk,2:  "++++++++++++++++++++++++++++++++++++++++++++++++";
    type:=StackTipus[#StackTipus];
    Prune(~StackTipus);
    K:=#type;

if K gt 1 then 
    type[K-1]`ProductOfQuotients:=[];
    type[K-1]`ProductOfQuotientsValuations:=[]; 
        
end if;    
    
    vprint montestalk,2:  "Analyzing type of order ",K;
    vprint montestalk,4:  "Phik=",type[K]`Phi;
    slope:=type[K]`cuttingslope;


///////////////////////////////////////     
// Computation of the Newton polygon //
//////////////////////////////////////
    np:=[];
    newtonpoints(~type, ~np);
    vprint montestalk,4:  "Points in the Newton polygon ", np;
    V:=NewtonPolygon(np);
    sides:=[];
    s:=LowerVertices(V);
    for i:=1 to #LowerSlopes(V)  do
           if LowerSlopes(V)[i] lt slope
       then
            Append(~sides,[LowerSlopes(V)[i],s[i][1],s[i][2],s[i+1][1],s[i+1][2]]);
       end if;
    end for;
    vprint montestalk,3: "Sides of Newton polygon:",sides;
    
    
//////////////////////////////     
// Computation of the index //
//////////////////////////////
    prevh:=0;	
    lengtha:=0;
    indexphi:=0;
    for  i:=#sides to 1 by -1 do  
	    Ei:=Integers()!(sides[i,4]-sides[i,2]);
        Hi:=Integers()!(sides[i,5]-sides[i,3]);
        hi:=-Numerator(sides[i,1]);
        ei:=Denominator(sides[i,1]);
    	indexphi:=indexphi+Ei*prevh+((-Ei*Hi-Ei+Hi+(Ei div ei))div 2);
    	prevh:=prevh-Hi;
	    lengtha:=lengtha+Ei;	
    end for;     
    

    ar:=sides[#sides,4]-sides[1,2];
    indexphi:=indexphi+slope*ar*(ar-1)/2; 
    indexphi:=indexphi*type[1]`d;
    if K gt 1 then 
        indexphi:=indexphi*&*[type[j]`f: j in [1..K-1]];         
    end if;
    indextotal:=indextotal+indexphi;

    vprint montestalk, 2: "Added  ", indexphi, " to the index";

    inferiors:=[* *];    
    for  i:=#sides to 1 by -1 do  // GRAN FOR  COSTATS
        
        vprint montestalk,2:  "----------------------";
        vprint montestalk,2:  "----------------------";
        vprint montestalk,2:  "Annalyzing side ",sides[i];
	    pa:=PolynomialRing(Integers())!1;
        ResidualPolynomial(type[1]`Pol,K,~type,sides[i],~pa);
        alfai:=Integers()!sides[i,2];
        betai:=Integers()!sides[i,3];        
        Ei:=Integers()!(sides[i,4]-alfai);
        Hi:=Integers()!(sides[i,5]-betai);
        hi:=-Numerator(sides[i,1]);
        ei:=Denominator(sides[i,1]);	
	    type[K]`h:=hi;
	    type[K]`e:=ei;
	    type[K]`slope:=-sides[i,1];        
        vprint montestalk,2:  "Slope: ",sides[i,1];
        vprint montestalk,2:  "Origin: (",alfai,",",betai,")";
        vprint montestalk,2:  "End point: (", sides[i,4], "," ,sides[i,5],")";
        vprint montestalk,2:  "----------------------";
        vprint montestalk,2:  "----------------------";
        
        
	    if Degree(pa) gt 1 then 
		      factors:=Factorization(pa);
	    else
		      factors:=[<pa/Coefficient(pa,Degree(pa)),1>];
	    end if;
        vprint montestalk,3: "Monic Residual Polynomial=",pa/Coefficient(pa,Degree(pa));
        
        vprint montestalk,2:  "The residual polynomial has ", #factors,"factors";            
        
        vprint montestalk,4:  "Factors of r.p.:=",factors;            
        
              // MIREM SI TOTS ELS TIPUS SERAN COMPLETS 
        
        totscomplets:=&and[x[2] eq 1: x in factors];
        
        vprint montestalk,5:  "All types complete?", totscomplets;
        
        if K gt 1 then         
            productofe:=&*[type[j]`e: j in[1..K-1]];
        else productofe:=1;
        end if;    

        ordenadai0:=betai-alfai*type[K]`VPhi;   

        if totscomplets then
             ordenadai:=ordenadai0;   
             for jjj:=alfai+1 to Integers()!sides[i,4]    do
                 ordenadai:=ordenadai-type[K]`slope-type[K]`VPhi;
                 orde:=ordenadai/productofe;   
                 for kkk:=1 to #type[K]`ProductOfQuotients do
                      xxx:= type[K]`ProductOfQuotients[kkk];
                      eee:= type[K]`ProductOfQuotientsValuations[kkk];
                      vvv:=orde+eee;
                      pq:=type[K]`Quotients[jjj]*xxx mod type[1]`Pol;
                    Append(~Basis, pq);                    
                    Append(~BasisValuations, vvv);
                 end for;
             end for;              
 
        vprint montestalk,5:  "All types are complete and Basis updated to ", Basis, " with valuations ", BasisValuations;                    
             
        end if;
        
        ordenadai:=sides[i,5]-type[K]`VPhi*sides[i,4];
        fmax:=Max([Degree(factors[ii,1]): ii in [1..#factors]]);
        cuamax:=type[K]`e*fmax-1;
        EnlargedPQ:=type[K]`ProductOfQuotients;
        EnlargedPQValuations:=type[K]`ProductOfQuotientsValuations;
        initiallengthPQ:=#EnlargedPQ;
            for jjj:=Integers()!sides[i,4]-1 to Integers()!sides[i,4]-cuamax by -1   do
                            ordenadai:=ordenadai+type[K]`slope+type[K]`VPhi;
                            orde:=ordenadai/productofe; 
                            for kkk:=1 to initiallengthPQ  do
                                        xxx:= EnlargedPQ[kkk];
                                        eee:= EnlargedPQValuations[kkk];
                                      Append(~EnlargedPQ, type[K]`Quotients[jjj]*xxx mod type[1]`Pol);
                                      Append(~EnlargedPQValuations, orde+eee);
                            end for;
                                 
            end for;              
                
        
        
        
        for ipetit:=1 to #factors do        // PETIT FOR PER ALS FACTORS DEL PA
              vprint montestalk,2:  "----------------------";
              vprint montestalk,2: "Analyzing a factor of the residual polynomial";
              vprint montestalk,2:  "psi=",factors[ipetit,1];
              vprint montestalk,2:  "----------------------";
              ta:=type;  
              for k in inferiors do Append(~ta[1]`DominatedTypes, [* k,-sides[i,1]*]); end for;
		      psi:=factors[ipetit,1];
		      aa:=factors[ipetit,2];
		      ta[K]`psi:=psi;
		      ta[K]`f:=Degree(psi);
              H:=((ta[K]`e)*ta[K]`VPhi+(ta[K]`h))*ta[K]`f;
        	  
              newside:=[-ta[K]`slope,0,H,0,0];
              td1:=0;                    
              if K gt 1 then texp(K,~ta,ta[K]`f,newside,~td1); end if;
	          if K eq 1 then
		          uipetit:=(ta[1]`Fq)!1;
		      else 		       
				    uipetit:=(ta[K]`z)^td1;
              end if;
		      fij:=psi*uipetit;                    
              newphi:=PolynomialRing(Integers()).1;
              Construct(K+1,~ta,fij,H,~newphi);
              newlevel:=rec<TypeLevel|>;
              newlevel:=ta[K];
	          newlevel`Phi:=newphi;
              newlevel`PhiPowers:=[newphi];
              for j:=1 to Floor(Log(2,Degree(ta[1]`Pol)/Degree(newphi))) do
                        Append(~newlevel`PhiPowers,newlevel`PhiPowers[j]^2);
              end for;  
              newlevel`d:=Degree(newphi);
		      newlevel`Phiadic, newlevel`Quotients:=Taylor(ta[1]`Pol,newphi,aa);
//              newlevel`ProductOfQuotients:=ta[K]`ProductOfQuotients;
//              newlevel`ProductOfQuotientsValuations:=ta[K]`ProductOfQuotientsValuations;  

              if aa  eq 1 then // PETIT IF ACABA-CONTINUA
		          	 vprint montestalk,2:  "Found a factor in order  ",K;
                     newlevel`VPhi:=ta[K]`e*ta[K]`f*(ta[K]`e*ta[K]`VPhi+ta[K]`h);
                     delete newlevel`Pol;
                     delete newlevel`Prime;
                     delete newlevel`DominatedTypes;
                     
                     if not(totscomplets) then
                        newlevel`ProductOfQuotients:=[EnlargedPQ[j]: j in [1..initiallengthPQ*ta[K]`e*ta[K]`f]];
                        newlevel`ProductOfQuotientsValuations:=[EnlargedPQValuations[j]: j in [1..initiallengthPQ*ta[K]`e*ta[K]`f]];
                         
                        vprint montestalk,5:  "A complete type with PQ updated to ", newlevel`ProductOfQuotients, " with valuations ",newlevel`ProductOfQuotientsValuations;                    
                        ordenadai:=betai+alfai*ta[K]`slope -newlevel`VPhi/ta[K]`e;   
                        orde:=ordenadai/productofe;  
                         lpq:=#newlevel`ProductOfQuotients;
                        for kkk:=1 to lpq do
                            xxx:= newlevel`ProductOfQuotients[kkk];
                            eee:= newlevel`ProductOfQuotientsValuations[kkk];
                            vvv:=orde+eee;
                            pq:=newlevel`Quotients[1]*xxx mod type[1]`Pol;
                            Append(~Basis, pq);
                            Append(~BasisValuations, vvv);
                        end for;
                        vprint montestalk,5:  "A complete type with Basis updated to ", Basis, " with valuations ",BasisValuations;                    
                     end if;        
                     

                     Append(~ta,newlevel); 
			         Append(~COMPLETETYPES,ta); 
                     Append(~inferiors,#COMPLETETYPES);
                     
                     
              else  //petit if
      		        if  ((ta[K]`e) eq 1) and (Degree(ta[K]`psi) eq 1) then //IF REFINA-AVANÇA
                        // REFINA
                        vprint montestalk,2:  "Refining";
			            newlevel`cuttingslope:=-hi/ei;
                        vprint montestalk,3:  "cuttingslope=",-hi/ei;
//                        newlevel`VPhi:=ta[K]`VPhi;
                        if K gt 1 then 
                                delete newlevel`Pol;
                                delete newlevel`Prime;
                                delete newlevel`DominatedTypes;
                        end if;
		                Prune(~ta);
                    else
                        // AVANCA
                        vprint montestalk,2:  "Proceeding to higher order";
                        ta[K]`b:=InverseMod(ta[K]`h,ta[K]`e);
                        delete newlevel`Pol;
                        delete newlevel`Prime;
                        delete newlevel`DominatedTypes; 
                        newlevel`VPhi:=ta[K]`e*ta[K]`f*(ta[K]`e*ta[K]`VPhi+ta[K]`h);
			            newlevel`cuttingslope:=0;
            		    newlevel`Fq:=ext<ta[K]`Fq| psi>;
                        newlevel`FqY:=PolynomialRing(newlevel`Fq);
                        AssignNames(~(newlevel`Fq),["z" cat IntegerToString(K)]);
                        AssignNames(~(newlevel`FqY),["Y" cat IntegerToString(K)]);
                        if Degree(fij) gt 1 then
    			             AssertAttribute(newlevel`Fq, "PowerPrinting", false) ;
                        end if;
		                newlevel`psi:=fij;
                        if Degree(fij) eq 1 then
                           newlevel`z:=Roots(fij)[1,1];
                        else
                            newlevel`z:=(newlevel`Fq).1;
                        end if;                         


                        newlevel`ProductOfQuotients:=[EnlargedPQ[j]: j in [1..initiallengthPQ*ta[K]`e*ta[K]`f]];
                        newlevel`ProductOfQuotientsValuations:=[EnlargedPQValuations[j]: j in [1..initiallengthPQ*ta[K]`e*ta[K]`f]];

                        vprint montestalk,5:  "PQ updated to ", newlevel`ProductOfQuotients, " with valuations ",newlevel`ProductOfQuotientsValuations;                    
                                     
                end if; //FINAL IF REFINA-AVANÇA
                
		        Append(~ta,newlevel);

		        
                Append(~StackTipus,ta);

                     
                            
                vprint montestalk,2:  "***********";	
              end if; // FINAL PETIT IF ACABA-CONTINUA
        end for;     // FINAL PETIT FOR PER ALS FACTORS DEL PA
    end for; // FINALGRAN FOR COSTATS
end while; // FINAL GRAN WHILE


vprint montestalk,1: "All the types are completed";
vprint montestalk,1: "The index is ", indextotal;
temps2:=Cputime(temps1);
vprint montestalk,1: "Ellapsed time: ",temps2;  


ttt:=Cputime();



prime:=COMPLETETYPES[1][1]`Prime;
for j:=1 to #Basis  do
  Basis[j]:=Basis[j] mod (prime^(1+Floor(BasisValuations[j])));
end for;

t3:=Cputime(ttt);

vprint montestalk,1: "Time reducing basis coefficients: ", t3;
vprint montestalk,1: "Max Valuation: ", Max(BasisValuations);



nprimes:=#COMPLETETYPES;

llistagens:=[];
if generators then 
    ttt:=Cputime();
    vprint montestalk,1: "Computing generators..."; 
    ComputeGenerators(~COMPLETETYPES,~llistagens);  
    vprint montestalk,1: "Generators computed in ", Cputime(ttt), " seconds"; 
end if;



    for j:=1 to nprimes do

        t:=COMPLETETYPES[j];
        K:=#t; 	
        primeid:=rec<PrimeIdeal|>;
        if generators then
            primeid`e:=t[K]`e;
            primeid`f:=t[K]`f;
            primeid`prime:=t[1]`Prime;
            primeid`generator:=llistagens[j];
        else 
            primeid`e:=(&*[t[j]`e: j in [1..K-1]]);
            primeid`f:=t[1]`d*(&*[t[j]`f: j in [1..K-1]]);    
        end if;    
        Append(~idealfactors,primeid);
    end for;    
    
//ft:=COMPLETETYPES;

temps3:=Cputime(temps1);
vprint montestalk,1: "Total time for determining the types:", temps3;

end intrinsic;



///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////


intrinsic ComputeGenerators(~COMPLETETYPES,~llistagens)
{}
alphas:=[];
Qx:=PolynomialRing(Rationals());
pol:=(COMPLETETYPES[1])[1]`Pol;
L:=NumberField(pol: Check:=false, Global:=true);
AssignNames(~Qx,[Sprint(Parent(pol).1)]);
pol:=Qx!pol;
nprimes:=#COMPLETETYPES;
prime:=(COMPLETETYPES[1])[1]`Prime;
for j:=1 to nprimes do
	   t:=COMPLETETYPES[j];
	   K:=#t-1;
	   (COMPLETETYPES[j][K+1])`e:=&*[(t[j])`e: j in [1..K]];
	   (COMPLETETYPES[j][K+1])`f:=t[1]`d*(&*[t[j]`f: j in [1..K]]);
	   v0:=0;
	   Value(t[K+1]`Phiadic[1],~t,K+1,~v0);
	   v1:=0;
	   Value(t[K+1]`Phiadic[2],~t,K+1,~v1);
	   w:=t[K+1]`VPhi;
	   slope:=v0-v1-w;
	   if slope gt 1 then 
		      H:=(w+1)/t[K]`e;
              M:=PolynomialRing(Integers()).1;
		      Construct(K+1,~t,(t[K]`FqY)!1,H,~M);
		      (COMPLETETYPES[j][K+1]`Phi)+:=M;
	   end if;
       _,InvPhi,_:=XGCD(PolynomialRing(Rationals())!COMPLETETYPES[j][K]`Phi,PolynomialRing(Rationals())!(pol));
	   al:=((COMPLETETYPES[j][K+1]`Phi)*Modexp(InvPhi,(t[K]`e)*(t[K]`f), pol)) mod pol;
	   Append(~alphas,al);
end for;

vprint montestalk,2: "Betas are computed";

for j:=nprimes to 2 by -1 do
	   t1:=COMPLETETYPES[j];
	   K1:=#t1-1;
	     for k in t1[1]`DominatedTypes do
                t2:=COMPLETETYPES[k[1]];
        		K2:=#t2-1;
                nkj:=&*[t1[j]`e: j in [K2..K1]]*t2[K2]`f*t2[K2]`e*(k[2]-t2[K2]`slope);
                nkj:=Integers()!nkj;
    			alphas[k[1]]:=(alphas[k[1]]*Modexp(alphas[j],nkj,pol)) mod pol;	
          end for;  
end for;

vprint montestalk,2: "Alphas are all adjusted";

for j:=1 to nprimes do
    coefs:=[Coefficient(alphas[j],ss): ss in [0..Degree(pol)-1]];
    dens:=[Denominator(x): x in coefs];	
    nums:=[Numerator(x): x in coefs];
    lcm:=LCM(dens);
    vp:=Valuation(lcm,prime);
    pvp:=prime^vp;
    num2:=[Integers()!(nums[j]*(lcm/dens[j])): j in [1..#nums]];
    gen:=(Qx!num2) div pvp;
    vals:=[Valuation(Denominator(x),prime)+1: x in Coefficients(gen) ];
    coefs:=Coefficients(gen);
    gen:=&+[(Integers()!Numerator(coefs[j]) mod (prime^vals[j]))/Denominator(coefs[j])*(L.1)^(j-1): j in [1..#coefs]];
    Append(~llistagens,gen);        
end for;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic localmontes(Pol::RngUPolElt,p::RngIntElt : Generators:=false )->SeqEnum
{ This function performs different computations related to the p-adic characteristics of the number field K
determined by the irreducible polynomial Pol. By default, it returns:\\

1) The p-index of the polynomial Pol, i.e.
\\
2) A list [w1,...,wn] of elements in K forming a p-integral basis of OK.  
\\

\\

3) a list of pairs [[e1,f1],...,[eg,fg]]
giving the ramification index and the residual degree of the 
prime ideals  appearing in the factorization of pOK.\\


\\


4) A list of generators for the prime ideals dividing pOK (only if  the option Generators:=true is given).
\\

}
K:=NumberField(Pol: Check:=false, Global:=true);

index, pnums, pdenoms, gens:=localmontesmatrix(Pol,p: generadors:=Generators);

www:=Cputime();


basis:=[ K![pnums[k ,x]: x in [Degree(Pol)..1 by -1]]/pdenoms[k]  : k in [1..Degree(Pol)]  ];

vprint montestalk,1: "Time coercing elements in number field: ", Cputime(www);

return index, basis, gens;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic localmontesmatrix(Pol::RngUPolElt,p::RngIntElt : generadors:=false, diag:="Integers" )->SeqEnum
{}
K:=NumberField(Pol: Check:=false, Global:=true);
Fp:=GF(p);
Fpy:=PolynomialRing(Fp);
fa:=Factorization(Fpy!Pol);
lifa:=[PolynomialRing(Integers())!Coefficients(n[1]): n in fa];
l:=#fa;
poln:= &*[lifa[k]^fa[k,2]: k in [1..l]];
G:=PolynomialRing(Integers())![Integers()!(x/p): x in Coefficients(Pol-poln)];
idealfactors:=[];
Basis:=[];
BasisValuations:=[];
StackTipus:=[];
typelevel:=rec<TypeLevel|>;
    for i:=1 to l do
        if (fa[i,2] eq 1 or Fpy!G mod fa[i,1] ne Fpy!0)
            then
                vprint montestalk,2:  "Found an ideal in order 0";
                primeid:=rec<PrimeIdeal|>;
                primeid`prime:=p;
                primeid`e:=fa[i,2];
                primeid`f:=Degree(fa[i,1]);
                primeid`generator:=Evaluate(lifa[i],K.1);
                Append(~idealfactors,primeid);
                _,qq:=Taylor(Pol,lifa[i],fa[i,2]-1);
                xx:=PolynomialRing(Integers()).1;
                trosbase:=[ qq[k]*xx^j: k in [1..#qq], j in [0..Degree(lifa[i])-1] ];
                Basis  :=Basis cat trosbase;
                BasisValuations cat:=[Rationals()!0: j in [1..#trosbase] ];
        else
		typelevel`Pol:=Pol;
		typelevel`Prime:=p;
		typelevel`Phi:=lifa[i];
        typelevel`PhiPowers:=[lifa[i]];
        for j:=1 to Floor(Log(2,Degree(Pol)/Degree(lifa[i]))) do
                        Append(~typelevel`PhiPowers,typelevel`PhiPowers[j]^2);
        end for;  

		typelevel`d:=Degree(lifa[i]);
		typelevel`VPhi:=0;
		typelevel`Phiadic,typelevel`Quotients:=Taylor(Pol,lifa[i], fa[i,2]);
        typelevel`ProductOfQuotients:=[PolynomialRing(Integers()).1^k: k in [0..typelevel`d-1]];
        typelevel`ProductOfQuotientsValuations:=[Rationals()!0:k in [0..typelevel`d-1]];
        

		typelevel`e:=0;
		typelevel`h:=0;
		typelevel`b:=0;
		typelevel`cuttingslope:=0;
		typelevel`DominatedTypes:=[* *];
		(typelevel`Fq):=ext<Fp|fa[i,1]>;
        if typelevel`d gt 1 then
        		AssertAttribute(typelevel`Fq, "PowerPrinting", false) ;
                AssignNames(~(typelevel`Fq),["z" cat IntegerToString(0)]);
        end if;
        typelevel`FqY:=PolynomialRing(typelevel`Fq);
        AssignNames(~(typelevel`FqY),["Y" cat IntegerToString(0)]);
        if Degree(fa[i,1]) eq 1 then
                           typelevel`z:=Roots(fa[i,1])[1,1];
        else
                            typelevel`z:=(typelevel`Fq).1;
        end if;
        Append(~StackTipus,[typelevel]);
        end if;
    end for;
indextotal:=0;    
if  #StackTipus gt 0 then
    montesaux(~StackTipus, ~idealfactors, ~indextotal,~Basis, ~BasisValuations : generators:=generadors);
end if;



    n:=Degree(Pol);
    SV:=[Floor(v): v in BasisValuations];
    contents:=[Content(x): x in Basis];
    contentsvals:=[Valuation(x,p): x in contents]; 
    SV:=[SV[k]-contentsvals[k]: k in [1..n]];
    H:=Max(SV);
  
    basis:=[p^(H-SV[k])*(Basis[k] div contents[k])  : k in [1..n]  ];
    basis:=[[Coefficient(basis[k],j)  :j in [n-1..0 by -1]] : k in [1..n]  ];

    
    A:=Matrix(Integers(),n,n,basis);
    
   vprint montestalk,1: "Largest Coefficient in Matrix:", Max([Abs(A[i,j]): i in [1..n],j in [1..n]]);

    tempsh1:=Cputime();

    if  diag eq "Integers" then    
        HA:=HermiteForm(A: Optimize:=false);
   
    else 
        AA:=ChangeRing(A,Integers(p^(H+1)));
        HA:=EchelonForm(AA);
        HA:=ChangeRing(HA,Integers());

    end if;

    vprint montestalk,1: "Largest Coefficient in Reduced Matrix:", Max([Abs(HA[i,j]): i in [1..n], j in [1..n]]);
    tempsh2:=Cputime(tempsh1);    
    vprint montestalk,1: "Time to find Hermite Form: ", tempsh2;

    pdenoms:=[];
    sumexponentspdenoms:=0;
    for i in [1..n] do 
        aa:=HA[i,i];
        vp,nonp:=Valuation(aa,p);
        Hmvp:=H-vp;
        pHmvp:=p^Hmvp;
        inv:=Modinv(nonp,pHmvp);
        Append(~pdenoms,pHmvp);
        sumexponentspdenoms+:=Hmvp;
        MultiplyRow(~HA,inv,i);
        HA[i,i]:=aa div nonp;
    end for;

    tempsh3:=Cputime(tempsh1);    
    vprint montestalk,1: "Time to simplify Hermite Form: ", tempsh3-tempsh2;




    HAA:=HermiteForm(HA: Optimize:=false);   
    tempsh4:=Cputime(tempsh1);    
    vprint montestalk,1: "Time to find second Hermite Form: ", tempsh4-tempsh3;


    
    pnums:=[ [ HAA[i,j] div HAA[i,i]: j in [1..n]]: i in [1..n]];



    if indextotal ne sumexponentspdenoms then 
       print "###############################################################################################";
       print "###############################################################################################";
       print "The Z-module generated by the output basis is not maximal  at the prime ",p ;
       print "Please, send  this example to guardia@ma4.upc.edu";
       print "###############################################################################################";
       print "###############################################################################################";       
       print "Pol=",Pol;
       
    end if;

    

if generadors then
    return  indextotal,pnums,pdenoms,idealfactors;
else 
    return  indextotal,pnums,pdenoms,[[x`e, x`f]: x in idealfactors];
end if;


end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////



intrinsic ResidualPolynomial(pol,k,~type, side, ~psi )
{}
if pol eq Parent(pol)!1 then psi:=PolynomialRing((type[1]`Fq))!1;
else 
	if pol eq type[1]`Pol then 
			dev:=(type[k]`Phiadic);
	else dev:=Taylor(pol,type[k]`Phi, Floor(Degree(pol)/type[k]`d) ); 
	end if;
	z:=(type[k]`z);	
	var:=PolynomialRing(type[k]`Fq).1;
	a:=Integers()!side[2];
	b:=Integers()!side[3];
	c:=Integers()!side[4];
	d:=Integers()!side[5];
	E:=Integers()!(c-a);
	H:=Integers()!(b-d);
	D:=Gcd(E,H);
	if k eq 1 then
		if D ne 0 then
			ee:=Integers()!(E/D);
			hh:=Integers()!(H/D);
			lim:=Floor(Min(D,((#dev)-a-1)/ee));		
			if lim lt 0 then psi:=PolynomialRing(Integers())!0; 
			else
				psi:=&+[ Evaluate(PolynomialRing(Integers())!(dev[a+j*ee+1] div (type[1]`Prime)^(b-j*hh)), z)* var^j : j in [0..lim]];
			end if;
		else 
			if a lt #dev then 
				psi:=Evaluate(PolynomialRing(Integers())!(dev[a+1] div (type[1]`Prime)^b),z);
			else
				psi:=0;
			end if;	
		end if;
       		 psi:=PolynomialRing(Parent(z))!psi;
	else	


         if D ne 0 then
			ee:=Integers()!(E/D);
			hh:=Integers()!(H/D);
			lim:=Floor(Min(D,(#dev-a-1)/ee));
			S:=PolynomialRing(type[k]`Fq)!0;
			for j:=0 to lim do
				aj:=dev[a+j*ee+1];
				if aj ne 0 then
					Hj:=(b-j*hh-(a+j*ee)*(type[k]`VPhi))/(type[k-1]`e);
					 S1j:=SideHeightSlope(Hj,-type[k-1]`slope);
					tj:=0;
					texp(k,~type, j,side,~tj);
 					uj:=(type[k]`z)^tj;
					pj:=PolynomialRing(type[k]`Fq).1;
					ResidualPolynomial(aj,k-1,~type,S1j,~pj);
					rj:=Evaluate(PolynomialRing(Parent(z))!pj, z);
					S:=S+uj*rj*var^j;
				end if;
			end for;
			psi:=S;
		else 
			if a lt #dev then 
				aj:=dev[a+1];
				Hj:=(b-a*(type[k]`VPhi))/(type[k-1]`e);
				S1j:=SideHeightSlope(Hj,-type[k-1]`slope);
				tj:=0;
				texp(k,~type, 0,side,~tj);
				uj:=(type[k]`z)^tj;
				pj:=PolynomialRing(type[k]`Fq).1;
				ResidualPolynomial(aj,k-1,~type,S1j,~pj);
				psi:=uj*Evaluate(PolynomialRing(Parent(z))!pj, z);
			else
				psi:=PolynomialRing(type[k]`Fq)!0;
			end if;	
		end if;
	end if; 
end if;
end intrinsic;



intrinsic Construct(k,~type, psi,H, ~phi )
{}
local d, alpha, coefs, coefis,fij,cc;
if k eq 2 then
    	d:=Degree(psi);
        Prime:=type[1]`Prime;        
	    alpha:=0;
        beta:=H;
	    while not(IsIntegral(beta)) do
		  beta:=beta-type[1]`slope;
		  alpha:=alpha+1;
	    end while;
        beta:=Integers()!beta; // Cal posar-ho per si beta=0
        coefs:=Coefficients(psi);
        coefs:=[Eltseq(c,type[1]`Fq): c in coefs]; 
	    if Degree(type[1]`psi) gt 1 then
            	coefsli:=[[Eltseq(u, PrimeField(type[1]`Fq)): u in c]:c in coefs];
                coefsli:=[PolynomialRing(Integers())!(c[1]): c in coefsli];
	    else
            	 coefsli:=[PolynomialRing(Integers())!Eltseq((type[1]`Fq)!c):c in coefs ];
        end if;
        
               
        phi:=&+[Integers()!(Prime^(beta-type[1]`h*j))*(coefsli[j+1])*(type[1]`Phi)^(j*type[1]`e): j in [0..d]];



        phi:=phi*(type[1]`Phi)^alpha;
         
else	
        d:=Degree(psi);
        alpha:=0;
        beta:=H;
	    while not(IsIntegral(beta)) do
	       	  beta:=beta-type[k-1]`slope;
		      alpha:=alpha+1;
    	end while;
        coefis:=Coefficients(psi);
	    side:=[-type[k-1]`slope, alpha, beta,0,0];
    	tj:=0;
	    texp(k-1, ~type,d,side,~ tj);
        uj:=(type[k-1]`z)^-tj;


	    fij:=(type[k-1]`Fq)!(Coefficient(psi,d)*uj);
    	if Degree(type[k-2]`psi) gt 1 then
	       	fij:=PolynomialRing(type[k-2]`Fq)!Eltseq(fij,type[k-2]`Fq);
	    end if;
    	cj:=PolynomialRing(Integers()).1;
	    h:=(beta-d*(type[k-1]`h)-(d*(type[k-1]`e)+alpha)*(type[k-1]`VPhi))/(type[k-2]`e);
        fij:=PolynomialRing(type[k-1]`Fq)!fij;
    	Construct(k-1,~type, fij,h ,~cj);


    	phi:=cj*(type[k-1]`Phi)^(d*type[k-1]`e);
    	for j:=d-1 to 0 by -1 do
    		if coefis[j+1] ne 0 then
	       		Hj:=beta-j*(type[k-1]`h)-(j*(type[k-1]`e)+alpha)*(type[k-1]`VPhi);
                tj:=0;
			    texp(k-1,~type,j,side,~tj);
    		    uj:=(type[k-1]`z)^-tj;
    			fij:=coefis[j+1]*uj;
    			if Degree(type[k-2]`psi) gt 1 then
	           			fij:=PolynomialRing(type[k-2]`Fq)!Eltseq(
                                -Coefficient(MinimalPolynomial(fij,type[k-1]`Fq),0),type[k-2]`Fq);
			    end if;
                cj:=PolynomialRing(Integers()).1;
                fij:=PolynomialRing(type[k-1]`Fq)!fij;
    			Construct(k-1,~type, fij,Hj/(type[k-2]`e) ,~cj);
               phi:=phi+cj*(type[k-1]`Phi)^(j*type[k-1]`e);	          

//             phi:=phi+cj*Phij[j+1];	          

//	       		phi:=phi+cj*Phij;	
		    end if;

	   end for;
       phi:=phi*(type[k-1]`Phi)^alpha;
end if;        
end intrinsic;


intrinsic texp(k, ~type,j,side, ~tj)
{}
h:=-Numerator(side[1]);
e:=Denominator(side[1]);
alpha:=side[2];
beta:=side[3];
H:=(beta-j*h-(alpha+j*e)*(type[k]`VPhi))/(type[k-1]`e);
S:=SideHeightSlope(H, -type[k-1]`slope);
tj:=Integers()!((S[2]-(type[k-1]`b)*(beta-j*h))/(type[k-1]`e));
end intrinsic;


intrinsic SideHeightSlope(height,slope)->SeqEnum
{}
	originx:=0;
	originy:=height;
	e:=Denominator(slope);
	h:=Numerator(slope);
	while not(IsIntegral(originy)) do
		  originx:=originx+1;
		  originy:=originy+slope;
	end while;
	endx:=originx+e*Floor(-height/h-originx/e);
	endy:=slope*endx+height;
return [slope, originx, originy, endx, endy];
end intrinsic;


//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//
//  Rutina FastTaylor
//  *  Calcula el phi-desenvolupament de pol fins a grau ell, però no calcula els quocients
//  *  Algoritme de pàg. 250 de "Modern Computational Algebra", de von zur Gathen.
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
intrinsic FastTaylor(pol,phipowers)->SeqEnum
{Compute the phi-adic expansion of pol, using the pre-computed given list of powers of phi}
if Degree(pol) lt Degree(phipowers[1])  then 
    return [pol];
end if; 

k:=Floor(Log(2,Degree(pol)/Degree(phipowers[1])))+1;  /* this is k/2 in the book */

quot,rem:=Quotrem(pol,phipowers[k]);

l1:=FastTaylor(quot,phipowers);
l2:=FastTaylor(rem,phipowers);
 
return l2 cat l1;

end intrinsic;



//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//
//  Rutina Taylor
//  *  Calcula el phi-desenvolupament de pol fins a grau ell, donant coeficients i quocients
//  *  S'usa per al càlcul de la base d'enters
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////

intrinsic Taylor(pol,phi,ell)->SeqEnum,SeqEnum
{}
quot:=pol;
Coeffs:=[];
Quos:=[];
for j:=0 to ell do 
  		quot,rem:=Quotrem(quot,phi);
  		Append(~Coeffs,rem);
        Append(~Quos,quot);
end for;
return Coeffs,Quos;
end intrinsic;


intrinsic newtonpoints(~type,~np)
{}
K:=#type;
n:=(type[K]`VPhi);
l:=(type[K]`Phiadic);
np:=[];
for i in [1..#l] do 
	aaa:=0;
	Value(l[i],~type,K, ~aaa); 
	if IsFinite(aaa) then 
		Append(~np,<i-1,aaa+(i-1)*n>);  
	end if;
end for;
end intrinsic;




intrinsic Value(pol, ~type, k, ~val )
{}
if pol eq 0 then val:=Infinity();
else
	Prime:=type[1]`Prime;
	if k eq 1 then 
   		val:=Integers()!Min([Valuation(c,Prime): c in Coefficients(pol)]);
	else  
		T:=type[k-1];
		n:=T`VPhi+T`slope;
		coefs:=Taylor(pol,T`Phi,Floor(Degree(pol)/Degree(T`Phi)));
		vals:=[0: i in [1..#coefs]];
		for i:=1 to #coefs do 
			if coefs[i] eq 0 then vals[i]:=-1;
			else Value(coefs[i],~type,k-1,~vals[i]);
			end if;
		end for;
		val:=Integers()!(T`e*Min([vals[i]+(i-1)*n: i in [1..#vals] | vals[i] ge 0 ]));
	end if;
end if;
end intrinsic;



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

function Arregla(pol,m)
cc:=Coefficients(pol);
mm:=RealField()!m/2;
for i:=1 to #cc do
 if Abs(cc[i]) gt mm then cc[i]:=cc[i] mod m;  end if;
end for;
return Parent(pol)!cc;
end function;




///////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////
// Funcions per crear tipus                                                                           //
///////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic EnlargeType( e, h,psi,~t, ~Y,~z)
{}
k:=#t;
t[k]`psi:=psi;
t[k]`h:=h;
t[k]`e:=e;
t[k]`slope:=h/e;
t[k]`b:=0;
t[k]`b:=InverseMod(t[k]`h,t[k]`e);
t[k]`cuttingslope:=0;	
if Degree(psi) eq 1 then
    t[k]`z:=Roots(psi)[1,1];
else
    t[k]`z:=Generator(t[k]`Fq);
end if;
H:=((t[k]`e)*t[k]`VPhi+(t[k]`h))*Degree(psi);
newside:=[-t[k]`slope,0,H,0,0];              
dd:=Degree(psi);
td1:=0;                    
if k gt 1 then texp(k,~t,dd,newside,~td1); end if;
if k eq 1 then
    uipetit:=(t[1]`Fq)!1;
else 		
    uipetit:=(t[k]`z)^td1;
    
end if;
fij:=psi*uipetit;                                
Phi3:=PolynomialRing(Integers()).1;
Construct(k+1,~t,fij,H,~Phi3);   
Append(~t,rec<TypeLevel|>);
t[1]`Pol:=Phi3;
t[k+1]`Phi:=Phi3;
t[k+1]`PhiPowers:=[Phi3];
for  r:=1 to k+1 do
  t[r]`PhiPowers:=[t[r]`Phi];
  for jj:=1 to Floor(Log(2,Degree(Phi3)/Degree(t[r]`Phi))) do
                        Append(~t[r]`PhiPowers,t[r]`PhiPowers[jj]^2);
  end for;   
end for;


t[k+1]`d:=Degree(Phi3);
for  r:=1 to k+1 do
  t[r]`Phiadic,t[r]`Quotients:=Taylor(t[1]`Pol,t[r]`Phi,Floor(t[1]`d/t[r]`d));
end for;
aaa:=0;
Value(t[k+1]`Phi,~t,k+1,~aaa);	
t[k+1]`VPhi:=aaa;
Fq0:=t[k]`Fq;
t[k+1]`Fq:=ext<Fq0|psi>;
if Degree(psi) gt 1 then
       AssertAttribute(t[k+1]`Fq, "PowerPrinting", false) ;
       AssignNames(~(t[k+1]`Fq),["z" cat Sprint(k)] );
end if;
Append(~z,Generator(t[k+1]`Fq));
t[k+1]`FqY:=PolynomialRing(t[k+1]`Fq);
AssignNames(~(t[k+1]`FqY),["Y" cat Sprint(k)] );
Append(~Y,(t[k+1]`FqY).1);
end intrinsic;





intrinsic InitializeType(p,psi)-> SeqEnum,SeqEnum,SeqEnum
{}
t:=[rec<TypeLevel|>];
Y:=[**];
z:=[**];
t[1]`Prime:=p;
((t[1])`Fq):=ext<GF(t[1]`Prime)| PolynomialRing(GF(t[1]`Prime))!psi>;
t[1]`FqY:=PolynomialRing(t[1]`Fq);
AssignNames(~(t[1]`FqY),["Y0"] );
Append(~Y,(t[1]`FqY).1);
t[1]`Phi:=PolynomialRing(Integers())!Coefficients(psi);
t[1]`PhiPowers:=[t[1]`Phi];
t[1]`Pol:=t[1]`Phi;
t[1]`Phiadic,t[1]`Quotients:=Taylor(t[1]`Pol,t[1]`Phi,1);
t[1]`d:=Degree(psi);
aaa:=0;
Value(t[1]`Phi,~t,1,~aaa);	
t[1]`VPhi:=aaa;
if Degree(psi) gt 1 then 
    AssertAttribute(t[1]`Fq, "PowerPrinting", false) ;      
    AssignNames(~(t[1]`Fq),["z0"] );
end if;
Append(~z,Generator(t[1]`Fq));
return t,Y,z;
end intrinsic;




intrinsic CreateRandomType(p,r)->SeqEnum
{}
l:=[];
s:=Random(2)+1;
fi0:=PolynomialRing(Integers())!RandomPrimePolynomial(PolynomialRing(GF(p)),s);
t,Y,z:=InitializeType(p,fi0);
for j:=1 to r do
    e:=Random(2)+1;
    h:=Random(10)+1;
    d:=GCD(e,h);
    e:=e/d; h:=h/d;
    f:=Random(2)+1;
    if (e*f eq 1) then f:=f+1; end if;
    test:=true;
    while test do
        psi:=RandomPrimePolynomial(PolynomialRing( t[j]`Fq),f);
        if f gt 1 or Coefficient(psi,0) ne CoefficientRing(psi)!0 then test:=false; end if;
    end while;
    vprint montestalk,1: "Psi",Sprint(j), "=",psi;
    EnlargeType(e,h,psi,~t,~Y,~z);
    vprint montestalk,2: "Degree=",Degree(t[1]`Pol);
end for;
return t;
end intrinsic;


intrinsic CreateRandomMultipleTypePolynomial(p,k,r,s)->RngUPolElt
{}
l:=[];
t:=1;
for j:=1 to k do
    Append(~l,CreateRandomType(p,r));
    end for;
pol:=&*[t[1]`Pol: t in l]+p^s;
while not IsIrreducible(pol) do pol:=pol+p^s; end while;
return pol;
end intrinsic;


intrinsic CombinePolynomialsWithDifferentPrimes(f1,p1,f2,p2,k)->RngUPolElt
{}
c1:=Coefficients(f1);
c2:=Coefficients(f2);
cc:=[CRT([c1[j],c2[j]],[p1^k,p2^k]):  j in [1..Degree(f1)+1]];
pol:=PolynomialRing(Integers())!cc;
return pol;
end intrinsic;




//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////
//
// Funcions de formateig
//
//////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////

intrinsic GlobalExpansion(Pol,t)->List
{Compute the coefficients of the multi-phi-adic expansion of pol. They are stored in a recursive list.}
k:=#t;
Phi:=t[k]`Phi;
m:=Floor(Degree(Pol)/Degree(Phi));
quot:=Pol;
Coeffs:=[* *];
        for j:=0 to m do 
  		    quot,rem:=Quotrem(quot,Phi);
  		    Append(~Coeffs,rem);
        end for;
if k gt 1 then
       tt:=Prune(t);  
       for j in [1..m+1]  do
           Coeffs[j]:= GlobalExpansion(Coeffs[j],tt);
       end for;
end if;
return Coeffs;
end intrinsic;


intrinsic Expand(coeffslist,t)->RngUPolElt
{This function is only useful to check the validity of expansions given by GlobalExpand}
if #coeffslist eq 0 then pol:=0;
else
    k:=#t;
    Phi:=t[k]`Phi;
    
    if k eq 1 then 
         pol:=&+[coeffslist[j]*Phi^(j-1): j in [1..#coeffslist]];
    else 
     tt:=Prune(t);
     pp:=0;
     cc:=[**];
             for j in [1..#coeffslist] do
                    pp:=Expand(coeffslist[j],tt);                    
                    Append(~cc,pp);
             end for;   
             pol:=&+[cc[j]*Phi^(j-1): j in [1..#coeffslist]];
             
    end if;
end if;
return pol;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//  Funcions per escriure TeX
////////////////////////////////////////////////////////////////////////
intrinsic ExpandTeX(pol,t)->Str 
{Write in TeX form the multi-phi-adic expansion of pol}
coeffslist:=GlobalExpansion(pol,t);
return ExpandTeXAux(coeffslist,t);
end intrinsic;

intrinsic ExpandTeXAux(coeffslist,t)->Str
{}
len:=#coeffslist;
p:=t[1]`Prime;
if len eq 0 then polstr:="0";
else
    k:=#t;
    Phi:=t[k]`Phi;

    polstr:="";
    if k eq 1 then 
           for j:=len to 1 by -1 do
             if coeffslist[j] ne 0 then 
               if Degree(coeffslist[j]) eq 0  then
                    ss:=Valuation(Integers()!coeffslist[j],p);cc:=Rationals()!coeffslist[j]/p^ss;
                    if ss eq 0 then stcc:="1"; else stcc:=Sprint(p) cat "^{" cat Sprint(ss) cat"}" ; end if;
                    if cc ne 1 then stcc:=stcc cat "\\cdot" cat Sprint(cc); end if;
                    
                else
                    stcc:=Sprint(coeffslist[j]);    
                end if;    
                polstr:=polstr cat "(" cat stcc  cat ")";
                if j gt 2 then polstr:=polstr cat "\\phi_" cat Sprint(k-1) cat "^{" cat Sprint(j-1) cat "}+"; end if;
                if j eq 2 then polstr:=polstr cat "\\phi_" cat Sprint(k-1) cat "+"; end if;
             end if;       
           end for;  
    else 
         tt:=Prune(t);
         pp:="";
         cc:=[];
         for j in [1..len] do
                    pp:=ExpandTeXAux(coeffslist[j],tt);
                    Append(~cc,pp);
         end for;   
         for j:=len to 1 by -1 do
             if cc[j] ne "0" then 
                polstr:=polstr cat "(" cat cc[j] cat ")";
                if j gt 2 then polstr:=polstr cat "\\phi_" cat Sprint(k-1) cat "^{" cat Sprint(j-1) cat "}+";  end if;
                if j eq 2 then polstr:=polstr cat "\\phi_" cat Sprint(k-1) cat "+"; end if;
             end if;       
           end for;           
    end if;
    lp:=#polstr;
    if polstr[lp] eq "+" then polstr:=Substring(polstr,1,lp-1); end if;
    if polstr[lp-1] eq "+" then polstr:=Substring(polstr,1,lp-2) cat ")"; end if;
end if;
return polstr;
end intrinsic;






intrinsic ExpandPhiTeX(k,t)->Str
{Write the phi-adic expansion of phi_k in TeX format}
polstr:="";
if k eq 0 then 
        coeffslist:=Coefficients(t[1]`Phi);
        len:=#coeffslist;
        p:=t[1]`Prime;
        for j:=len to 1 by -1 do
             if coeffslist[j] ne 0 then 
                    ss:=Valuation(Integers()!coeffslist[j],p);cc:=Rationals()!coeffslist[j]/p^ss;
                    if ss eq 0 then stcc:="1"; else stcc:=Sprint(p) cat "^{" cat Sprint(ss) cat"}" ; end if;
                    if cc ne 1 then stcc:=stcc cat "\\cdot" cat Sprint(cc); end if;
             else stcc:="0";
             end if;    
                polstr:=polstr cat "(" cat stcc  cat ")";
                if j gt 2 then polstr:=polstr cat "x" cat  "^{" cat Sprint(j-1) cat "}+"; end if;
                if j eq 2 then polstr:=polstr cat "x" cat  "+"; end if;
        end for;  
else 
    pol:=t[k+1]`Phi;
    t1:=[t[j]: j in [1..k] ];
    polstr:=ExpandTeX(pol,t1);
end if;    
return "\\phi_" cat Sprint(k) cat "=" cat polstr cat ";";
end intrinsic;


intrinsic ExpandAllPhiTeX(t)->Str 
{Write in TeX format the phi-adic expansion of all the phi in the type}
polstr:="\\phi_0=" cat ExpandPhiTeX(0,t);
for k in [2..#t] do
    st:="\\phi_" cat Sprint(k-1) cat "=" cat  ExpandPhiTeX(k-1,t);
    polstr:=polstr cat "\\\\" cat st;
end for;
return polstr;
end intrinsic;




////////////////////////////////////////////////////////////////////////
//  Funcions per escriure Magma
////////////////////////////////////////////////////////////////////////
intrinsic ExpandMagma(pol,t)->Str
{Write in Magma form the multi-phi-adic expansion of pol}
coeffslist:=GlobalExpansion(pol,t);
return ExpandMagmaAux(coeffslist,t);
end intrinsic;

intrinsic ExpandMagmaAux(coeffslist,t)->Str
{}
len:=#coeffslist;
p:=t[1]`Prime;
if len eq 0 then polstr:="0";
else
    k:=#t;
    Phi:=t[k]`Phi;
    polstr:="";
    if k eq 1 then 
           for j:=len to 1 by -1 do
             if coeffslist[j] ne 0 then 
               if Degree(coeffslist[j]) eq 0  then
                    ss:=Valuation(Integers()!coeffslist[j],p);cc:=Rationals()!coeffslist[j]/p^ss;
                    if ss eq 0 then stcc:="1"; else stcc:=Sprint(p) cat "^" cat Sprint(ss)  ; end if;
                    if cc ne 1 then stcc:=stcc cat "*" cat Sprint(cc); end if;
                    
                else
                    stcc:=Sprint(coeffslist[j]);    
                end if;    
                polstr:=polstr cat "(" cat stcc  cat ")";
                if j gt 2 then polstr:=polstr cat "*phi" cat Sprint(k-1) cat "^" cat Sprint(j-1) cat "+"; end if;
                if j eq 2 then polstr:=polstr cat "*phi" cat Sprint(k-1) cat "+"; end if;
             end if;       
           end for;  
    else 
         tt:=Prune(t);
         pp:="";
         cc:=[];
         for j in [1..len] do
                    pp:=ExpandMagmaAux(coeffslist[j],tt);
                    Append(~cc,pp);
         end for;   
         for j:=len to 1 by -1 do
             if cc[j] ne "0" then 
                polstr:=polstr cat "(" cat cc[j] cat ")";
                if j gt 2 then polstr:=polstr cat "*phi" cat Sprint(k-1) cat "^" cat Sprint(j-1) cat "+";  end if;
                if j eq 2 then polstr:=polstr cat "*phi" cat Sprint(k-1) cat "+"; end if;
             end if;       
           end for;           
    end if;
    lp:=#polstr;
    if polstr[lp] eq "+" then polstr:=Substring(polstr,1,lp-1); end if;
    if polstr[lp-1] eq "+" then polstr:=Substring(polstr,1,lp-2) cat ")"; end if;
end if;
return polstr;
end intrinsic;


intrinsic ExpandPhiMagma(k,t)->Str 
{Write the phi-adic expansion of phi_k in Magma format}
if k eq 0 then return Sprint(t[1]`Phi);
else 
    pol:=t[k+1]`Phi;
    t1:=[t[j]: j in [1..k] ];
    return ExpandMagma(pol,t1);
end if;    

end intrinsic;


intrinsic ExpandAllPhiMagma(t)->Str
{Write in Magma format the phi-adic expansion of all the phi in the type}
polstr:="";
for k in [1..#t] do
    st:=ExpandPhiMagma(k-1,t);
    st:="phi" cat Sprint(k-1) cat ":=" cat st cat ";           ";
    polstr:=polstr cat st;
end for;
return polstr;
end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////
//
//      Checking routines (for the index and generators of the ideals)
//
////////////////////////////////////////////////////////////////////////////////////////
function CheckIndex(pol,primer)
K<t>:=NumberField(pol);
OK:=MaximalOrder(K);
print "ZK calculat";
d:=Discriminant(OK);
d2:=Discriminant(pol);
return (Valuation(d2,primer)-Valuation(d,primer)) div 2;
end function;

function Check(pol,primer)
K<t>:=NumberField(pol);
OK:=MaximalOrder(K);
print "ZK calculat";
d1:=Discriminant(pol);
dd:=Discriminant(OK);
n:=Degree(K);
l:=Factorization(primer*OK);
print "descomp=",l;
print "Graus residuals:=",[Degree(x[1]): x in l];
l,b,c:=localmontes(pol,primer);
print "Graus montes:=",[x`f: x in l];
print "Ramificacio montes:=",[x`e: x in l];
gens:=[(K![Coefficient(x`generator,i): i in [0..(n-1)]]): x in l];
[IsIntegral(x): x in gens];
[Valuation(Norm(x),primer): x in gens];
ids:=[gen*OK+primer*OK: gen in gens];
 [Factorization(id): id in ids];
 print "index=", (Valuation(d1,primer)-Valuation(dd,primer))/2;
print "indexmontes=",b;
return 1;
end function;




