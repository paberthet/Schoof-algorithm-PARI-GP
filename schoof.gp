\\Fonctions pour générer les polynômes de division
global(x,y);

elldivpolr(e,n) = {
	local(ans=elldivpol0(e,n));
	if(n%2==1,ans,ans*(2*y+e[1]*x+e[3]));
}

elldivpol0(e,n) = {
	local(m,a1,a2,a3,a4,a6,t1,t2,f1,f2,psi24);
	a1=e[1];a2=e[2];a3=e[3];a4=e[4];a6=e[5];
	f1=x^3+a2*x^2+a4*x+a6; f2=a1*x+a3;
	n=abs(n);
	if(n==0,return(0));
	if(n==1,return(1));
	if(n==2,return(1));
	if(n==3,return(3*x^4+(a1^2+4*a2)*x^3+(3*a1*a3+6*a4)*x^2+(3*a3^2+12*a6)*x+a1^2*a6-a1*a3*a4+a2*a3^2+4*a2*a6-a4^2));
	if(n==4,return(2*x^6+(a1^2+4*a2)*x^5+(5*a1*a3+10*a4)*x^4+(10*a3^2+40*a6)*x^3+(10*a1^2*a6-10*a1*a3*a4+10*a2*a3^2+40*a2*a6-10*a4^2)*x^2+(a1^4*a6-a1^3*a3*a4+a1^2*a2*a3^2+8*a1^2*a2*a6-a1^2*a4^2-4*a1*a2*a3*a4-a1*a3^3-4*a1*a3*a6+4*a2^2*a3^2+16*a2^2*a6-4*a2*a4^2-2*a3^2*a4-8*a4*a6)*x+a1^3*a3*a6-a1^2*a3^2*a4+2*a1^2*a4*a6+a1*a2*a3^3+4*a1*a2*a3*a6-3*a1*a3*a4^2+2*a2*a3^2*a4+8*a2*a4*a6-a3^4-8*a3^2*a6-2*a4^3-16*a6^2));
	\\ general case, use recursion
	\\ If n is odd, n=2m+1:
	if(n%2==1,m=(n-1)/2;
	t1=elldivpol0(e,m+2)*elldivpol0(e,m)^3;
	t2=elldivpol0(e,m-1)*elldivpol0(e,m+1)^3;
	psi24=(4*f1+f2^2)^2;
	if(m%2==1,return(t1-psi24*t2),return(psi24*t1-t2)));
	\\ Now n is even, n=2m:
	m=n/2;
	t1=elldivpol0(e,m+2)*elldivpol0(e,m-1)^2;
	t2=elldivpol0(e,m-2)*elldivpol0(e,m+1)^2;
	elldivpol0(e,m)*(t1-t2);
}





\\ Lois sur l'anneau R ###########################################################################################################################################################################
\\testées ok

\\ Attention ,les P1 , P2 de cette section ne sont pas des points, ce sont des éléments de R vu sous la forme (F_q[X])^2
add_law(P1,P2) = {
	my(p11,p12,p21,p22,S);
	p11 = P1[1];
	p12 = P1[2];
	p21 = P2[1];
	p22 = P2[2];
	S = [p11+p21,p12+p22];
	return(S);
}

mul_law(P1,P2,E,mod) = {
	my(p11,p12,p21,p22,r1,r2,A,B);
	p11 = Mod(P1[1],mod);
	p12 = Mod(P1[2],mod);
	p21 = Mod(P2[1],mod);
	p22 = Mod(P2[2],mod);
	A = E[1];
	B = E[2];
	
	r1 = p11*p21 + p12*p22*( 'x^3 + A*'x + B);
	r2 = p11*p22 + p12*p21;
	return([r1,r2]);
}

expo_law(P1,q,E,mod) = {
	my(Q,bin);
	Q = [1,0];
	bin = binary(q);
	for(i=1,#bin,
		Q = mul_law(Q,Q,E,mod);
		if(bin[i]==1,Q = mul_law(P1,Q,E,mod)
		);
	);
	return(Q);	
}





div_law(P1,P2,E) = {
	my(p11,p12,p21,p22,r1,r2,A,B);
	p11 = P1[1];
	p12 = P1[2];
	p21 = P2[1];
	p22 = P2[2];
	A = E[1];
	B = E[2];
	
	\\print("P2 :",P2,"\n p22 : ",p22);
	diviseur = p21^2-('x^3+A*'x+B)*(p22^2);
	\\print("diviseur:\n",diviseur);
	r1 = p11*p21-p12*p22*('x^3+A*'x+B);
	\\print("r1:\n",r1);
	r2 = p12*p21-p11*p22;
	\\print("r2:\n",r2);
	r1 = r1/diviseur; 
	r2 = r2/diviseur; 
	return ([r1,r2]);
}








\\ Addition sur la courbe elliptique ###################################################################################################################################################

\\add_ell est ok
add_ell(P,Q,E,mod) = {
	my(R,x_r,y_r, x_p, y_p, x_q,y_q,A,B);
	\\ x_r,y_r, x_p, y_p, x_q,y_q sont tous des éléments de R, donc des couples de (F_q[X])²
	\\ on considère que le point inifini est Poo=[oo,oo] (et non pas [[oo,oo],[oo,oo]])
	
	x_p = P[1];
	y_p = P[2];
	x_q = Q[1];
	y_q = Q[2];
	A = [E[1],0];
	B = E[2];
	
	if(x_p == oo, return(Q),if(x_q == oo, return(P)));
	
	if(!(x_p == x_q), 
		x_r = div_law(add_law(y_p,(-1)*y_q ), add_law(x_p, (-1)*x_q ),E);
		y_r = x_r;
		x_r = mul_law(x_r,x_r,E,mod);
		x_r = add_law(x_r ,(-1)* x_p);
		x_r = add_law(x_r, (-1)* x_q);
		y_r = mul_law(y_r, add_law(x_p, (-1)*x_r),E,mod);
		y_r = add_law(y_r , (-1)*y_p),    \\else x_p==x_q
		
		if((y_p == y_q)&&(lift(y_p)!=[0,0]), \\si les deux points sont égaux
		x_r = 3 * mul_law(x_p,x_p,E,mod) + A;
		x_r = div_law(x_r , 2 * y_p,E);
		y_r = x_r;
		x_r = mul_law(x_r , x_r,E,mod);
		x_r = add_law(x_r , (-2)*x_p);
		y_r = mul_law(y_r, add_law(x_p , (-1 )*x_r),E,mod);
		y_r = add_law(y_r , (-1)*y_p),   \\else les deux points sont opposés

		x_r = oo;
		y_r = oo;
		
		);
	);
	
	R = [x_r , y_r];
	return(R);
}




\\ Double and add, agit sur les points de la courbe elliptique. ##################################################################################################################################
\\ finalement remplacée par div_pol_mul
double_and_add(P,k,E,mod) = {
	my(Q, bin);
	bin = binary(k);
	Q = [ oo , oo ];
	for(i=1,#bin,
		Q = add_ell(Q,Q,E,mod);
		if(bin[i]==1,Q = add_ell(P,Q,E,mod)
		);
		
	);
	return(Q);
}

\\ calcul de nP et de -nP
div_pol_mul(P,k,E,DIV_POL,mod) = {
	my(e,x_kp,y_kp);
	\\print("K :\n",k);
	if(k==1,return(P));
	if(k<0,
		Q = div_pol_mul(P, (-1)*k,E, DIV_POL, mod);
		return([Q[1],(-1)*Q[2]]);
	);
	e = [0,0,0,E[1],E[2]];
	phi_k = mapget(DIV_POL,k);  \\elldivpolr(e,k);
	phi_km1 = mapget(DIV_POL,k-1);  \\elldivpolr(e,k-1);

	phi_kp1 = mapget(DIV_POL,k+1);  \\elldivpolr(e,k+1);

	phi_2k = mapget(DIV_POL,2*k);  \\elldivpolr(e,2*k);
	
	if(k%2==1,
	
		\\then
	
		x_kp = [ Mod('x,mod) - (phi_km1*phi_kp1)*('x^3+E[1]*'x+E[2])/(y^2*(phi_k)^2),Mod(0,mod)];
		
		y_kp = [Mod(0,mod),Mod((phi_2k),mod)/Mod((y*2*(phi_k)^4),mod)];
		
		return([x_kp,y_kp]),
		
		\\else
	
		x_kp = [ Mod('x,mod) - (phi_km1*phi_kp1)*(y^2)/(('x^3+E[1]*'x+E[2])*(phi_k)^2),Mod(0,mod)];
		
		y_kp = [Mod(0,mod),Mod((phi_2k)*(y^4),mod)/Mod((('x^3+E[1]*'x+E[2])^2)*(y*2*(phi_k)^4),mod)];
		
		return([x_kp,y_kp]);
	
	);
}






frob_ell(P,q,E,mod) = {
	my(p1,p2,r1,r2);
	p1 = P[1];
	p2 = P[2];
	r1 = expo_law(p1,q,E,mod);
	r2 = expo_law(p2,q,E,mod);
	return([r1,r2]);
}




\\ P(x,y) \in (Fq)² <=> P((x,0),(0,1)) \in R^2 i.e. ((F_q[X])²)²










\\génère une liste de nombres premiers différents de q, tels que le produit de ces nombres soit supérieur à 4 * sqrt(q)
gen_s_and_div_pols( q , e ) = {
	my(S, prim, product, L, M);
	S = List();
	prim = 3;
	listput(S,prim);
	product = prim;
	\\prim=3;
	while(product <= 4 * sqrt(q),
		prim = nextprime(prim + 1);
		if(q % prim==0 , prim = nextprime(prim + 1));
		listput(S , prim);
		product *= prim;
	);

	M = Map();
	\\Il nous faut des polynômes de division pour trois utilités différentes:
		\\ - travailler modulo phi_l pour tout l dans la liste des nombres premiers, il nous faudra donc au maximum phi_l pour le plus grand des l
		\\ - multiplier par q mod l avec |q_l|<l/2 (la multiplication par k nécessite phi_k, phi_k-1, phi_k+1 et phi_2k il nous faudra donc ici au maximum phi_2*l/2 soit phi_l pour le plus grand des l
		\\ - multiplier par t_l avec t_l \in [1,(l-1)/2], il nous faudra donc au maximum phi_2*(l-1)/2 soit phi_l-1 pour le plus grand des l
	\\En conclusion, le "plus grand" polynôme de division dont nous aurons besoin sera phi_l pour le plus grand des l de la liste S.
	for(i=0,S[#S],
		mapput(M,i,elldivpolr(e,i));
	);
	return([S,M]);
}




default(parisize,"100M");

schoof(E,q) = {

	my(S ,l ,M ,P ,P_prime ,e ,y ,t_l ,w,a );
	a = ffgen(q,v);
	e = [0,0,0,E[1],E[2]];
	P = [[a^0*'x,0],[0,a^0]];  
	[S,DIV_POL] = gen_s_and_div_pols( q , e);
	\\print("S :\n",S);
	\\print("Div_pol :\n", DIV_POL);
	L = List(); \\ liste des Mod(t,l)	
	
	

	
	\\autres cas:
	for(i = 2, #S,
		trouve = 0;
		
		\\calcul de q_l = q mod l avec |q_l|<l/2
		
		l = S[i];
		q_l = q % l;
		if(q_l>=(l/2),q_l=q_l-l);

		\\récupération du polynôme de division phi_l du polynôme de division
		phi_l = mapget(DIV_POL,l);  \\elldivpolr(e,l);
		
		P_mod_phi_l = Mod(P,phi_l);

		frob2p = frob_ell(frob_ell(P_mod_phi_l,q,E,phi_l),q,E,phi_l);

		qlp = div_pol_mul(P_mod_phi_l,q_l,E,DIV_POL,phi_l);
		
		
		if(frob2p[1] != qlp[1] ,
			for(t = 1, (l-1)/2,

				Pqt = div_pol_mul(P_mod_phi_l,t,E,DIV_POL,phi_l);
				Pqt = frob_ell(Pqt,q,E,phi_l);	
				
							
				\\ test si Pqt frob2p et qlp sont alignés ils sont ici distincts
				if(mul_law(add_law(frob2p[2],(-1)*Pqt[2]),add_law((-1)*qlp[1],frob2p[1]),E,phi_l)==mul_law(add_law((-1)*qlp[2],frob2p[2]),add_law(frob2p[1],(-1)*Pqt[1]),E,phi_l),
					\\print(" listput a");
					\\print("\nfrob2p :\n",frob2p,"\nqlp :\n",qlp);
					listput(L,1 + q + Mod(t,l));
					trouve = 1;
					break();
				);
				
				\\test si -Pqt fro2p et qlp sont alignés	
				if(mul_law(add_law(frob2p[2],Pqt[2]),add_law(qlp[1],(-1)*frob2p[1]),E,phi_l)==mul_law(add_law(qlp[2],(-1)*frob2p[2]),add_law(frob2p[1],(-1)*Pqt[1]),E,phi_l),
					\\print(" listput b");
					listput(L,1 + q - Mod(t,l));
					trouve = 1;
					break();
				);
				
				
			);
		);
		if( trouve == 0 ,
			w;
			if(issquare(Mod(q_l,l),&w)==0,
				\\then
				\\print(" listput c");
				listput(L,1 + q - Mod(0,l));
				trouve = 1;
			);
			if(trouve==0,
				
				wP = div_pol_mul(P_mod_phi_l,lift(w),E,DIV_POL,phi_l);
				wP = frob_ell(wP,q,E,phi_l);
				if(wP == frob2p,
					\\then
					\\print(" listput d");
					listput(L,1 + q - 2*w);
					trouve = 1,
					\\else
					if(wP == [frob2p[1],(-1)*frob2p[2]],
						\\then
						\\print(" listput e");
						listput(L,1 + q + 2*w),
						\\else
						listput(L,1 + q - Mod(0,l));
					);
				);

			);
		);
		\\print("\n");
	);
	\\print("liste : ",L);
	\\t = lift(chinese(L));
	t = chinese(L);
	N = t.mod;
	t = lift(t);
	while( t < (q+1-2*sqrt(q)) ,t = t + N );
	return(t);
}






\\########################################################################### Tests ###########################################################################

\\cardinal = schoof([Mod(5,37),Mod(0,37)],37); \\26
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(0,37),Mod(9,37)],37); \\27
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(0,37),Mod(6,37)],37); \\28
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(1,37),Mod(12,37)],37); \\29
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(2,37),Mod(2,37)],37); \\30
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(2,37),Mod(8,37)],37); \\31
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(3,37),Mod(6,37)],37); \\32
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(1,37),Mod(13,37)],37); \\33
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(1,37),Mod(18,37)],37); \\34
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(1,37),Mod(8,37)],37); \\35
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(1,37),Mod(0,37)],37); \\36
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(0,37),Mod(5,37)],37); \\37
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(1,37),Mod(5,37)],37); \\38
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(0,37),Mod(3,37)],37); \\39 
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(1,37),Mod(2,37)],37); \\40
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(1,37),Mod(16,37)],37); \\41
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(1,37),Mod(9,37)],37); \\42
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(2,37),Mod(9,37)],37); \\43
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(1,37),Mod(7,37)],37); \\44
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(2,37),Mod(14,37)],37); \\45
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(1,37),Mod(11,37)],37); \\46
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(3,37),Mod(15,37)],37); \\47
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(0,37),Mod(1,37)],37); \\48
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(0,37),Mod(2,37)],37); \\49
\\print("Cardinal de E[Fq] : ",cardinal);

\\cardinal = schoof([Mod(2,37),Mod(0,37)],37); \\50
\\print("Cardinal de E[Fq] : ",cardinal);






\\cardinal = schoof([Mod(3,1031),Mod(2,1031)],1031);        \\1 018
\\cardinal = schoof([Mod(3,32771),Mod(2,32771)],32771);     \\33 117
\\cardinal = schoof([Mod(1,65537),Mod(5,65537)],65537);     \\65 460
\\cardinal = schoof([Mod(1,100003),Mod(5,100003)],100003);  \\99 707
\\cardinal = schoof([Mod(1,131101),Mod(5,131101)],131101);  \\131 132
\\cardinal = schoof([Mod(2,190027),Mod(6,190027)],190027);  \\190 183
\\dinal = schoof([Mod(1,333517),Mod(2,333517)],333517);    \\ 332 640 utilise jusqu'à l=13 dans la liste des nombres premiers
\\print("Cardinal de E[Fq] : ",cardinal);

 
\\generateur = ffgen(25,'v);
\\cardinal = schoof([generateur^2,generateur^6],25); \\ 27

\\generateur = ffgen(49,'v);
\\cardinal = schoof([generateur^2,generateur^6],49); \\ 55

\\generateur = ffgen(125,'v);
\\cardinal = schoof([generateur^10,generateur^15],125); \\ 108

\\generateur = ffgen(625,'v);
\\cardinal = schoof([generateur^10,generateur^15],625); \\ 577

\\generateur = ffgen(1331,'v);
\\cardinal = schoof([generateur^10,generateur^15],1331); \\ 1 274
 
\\generateur = ffgen(13^4,'v);
\\cardinal = schoof([generateur^10,generateur^15],13^4); \\ 28 800

generateur = ffgen(19^4,'v);
cardinal = schoof([generateur^10,generateur^15],19^4); \\ 130 969


\\cardinal = schoof([Mod(1,414446216318822543),Mod(1,414446216318822543)],414446216318822543);

print("Cardinal de E[Fq] : ",cardinal);

