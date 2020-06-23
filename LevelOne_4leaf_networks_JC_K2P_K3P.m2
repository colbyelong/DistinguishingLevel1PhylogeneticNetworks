--This Macaulay2 file contains the invariants referenced in the proof of Lemmas 1 and 2
--in the paper "Distinguishing Level-1 Phylogenetic Networks On the Basis of Data Generated
--under Markov Processes" and the code to verify that these invariants vanish on the 
--appropriate varieties.

--The 4-leaf level-1 networks are numbered as follows
  --1-3: Tree Networks 
  --4-9: Triangle Networks (undirected)
  --10-21: 4-cycle Networks (semi-directed)
  --22-24: Double Triangle Networks (undirected)

--In order to run the code under each set of constraints (JC, K2P, or K3P), uncomment the 
--appropriate hash table "x" below.

--The implementation of the randomized algorithm described in the paper
--and the code to actually find distinguishing invariants 
--are at the end of the file.


restart;

A = (1,1);C = (1,-1);G = (-1,1); T = (-1,-1);

L = 
{(A,A,A,A),(A,A,C,C),(A,A,G,G),(A,A,T,T),(A,C,A,C),(A,C,C,A),(A,C,G,T),(A,C,T,G),
(A,G,A,G),(A,G,C,T),(A,G,G,A),(A,G,T,C),(A,T,A,T),(A,T,C,G),(A,T,G,C),(A,T,T,A),
(C,A,A,C),(C,A,C,A),(C,A,G,T),(C,A,T,G),(C,C,A,A),(C,C,C,C),(C,C,G,G),(C,C,T,T),
(C,G,A,T),(C,G,C,G),(C,G,G,C),(C,G,T,A),(C,T,A,G),(C,T,C,T),(C,T,G,A),(C,T,T,C),
(G,A,A,G),(G,A,C,T),(G,A,G,A),(G,A,T,C),(G,C,A,T),(G,C,C,G),(G,C,G,C),(G,C,T,A),
(G,G,A,A),(G,G,C,C),(G,G,G,G),(G,G,T,T),(G,T,A,C),(G,T,C,A),(G,T,G,T),(G,T,T,G),
(T,A,A,T),(T,A,C,G),(T,A,G,C),(T,A,T,A),(T,C,A,G),(T,C,C,T),(T,C,G,A),(T,C,T,C),
(T,G,A,C),(T,G,C,A),(T,G,G,T),(T,G,T,G),(T,T,A,A),(T,T,C,C),(T,T,G,G),(T,T,T,T)};

x = hashTable{A => 0, C => 1, G => 1, T => 1};--JC
--x = hashTable{A => 0, C => 1, G => 2, T => 1};--K2P
--x = hashTable{A => 0, C => 1, G => 2, T => 3};--K3P

y = hashTable{A => 0, C => 1, G => 2, T => 3};


L1 = toList apply(L,i->q_(y#(i#0),y#(i#1),y#(i#2),y#(i#3)));
L2 = {a_0,a_1,a_2,a_3,
      b_0,b_1,b_2,b_3,
      c_0,c_1,c_2,c_3,
      d_0,d_1,d_2,d_3,
      e_0,e_1,e_2,e_3,
      f_0,f_1,f_2,f_3,
      g_0,g_1,g_2,g_3,
      h_0,h_1,h_2,h_3,
      j_0,j_1,j_2,j_3,
      k_0,k_1,k_2,k_3,
      l_0,l_1,l_2,l_3};

R = QQ[(L2|L1), MonomialOrder=> Eliminate 44];

L1 = toList apply(L,i->q_(y#(i#0),y#(i#1),y#(i#2),y#(i#3)));

-------------------------------------------------------------
-------------------------------------------------------------
----Parameterizations and substitution maps------------------
-------------------------------------------------------------
-------------------------------------------------------------

--Trees (1-3)

Topos = {(1, 2, 3, 0), (2, 1, 3, 0), (1, 0, 3, 2)};

     
for j from 0 to 2 do{
    ll = (Topos#j)#0,
    ul = (Topos#j)#1,
    ur = (Topos#j)#2,
    lr = (Topos#j)#3,
    Par_(j + 1) =toList apply(L,i -> a_(x#(i#lr))*b_(x#(i#ll))*c_(x#(i#ul))*d_(x#(i#ur))*g_(x#(i#ul#0*i#3#0,i#ul#1*i#ur#1))); 
    Eqn_(j + 1) = L1 - Par_(j + 1);
    PAR_(j + 1) = matrix{{submatrix((vars R), 0..43),matrix{Par_(j + 1)}}};
};


--4-leaf triangle networks (4-9)

Topos = {(1, 2, 3, 0), (2, 1, 3, 0), (3, 2, 1, 0), (1, 0, 3, 2), (1, 2, 0, 3), (3, 0, 1, 2)};

     
for j from 0 to 5 do{
    ll = (Topos#j)#0,
    ul = (Topos#j)#1,
    ur = (Topos#j)#2,
    lr = (Topos#j)#3,
    Par_(j + 4) = toList apply(L,i-> a_(x#(i#lr))*b_(x#(i#ll))*c_(x#(i#ul))*d_(x#(i#ur))*f_(x#(i#ul))*g_(x#(i#lr#0*i#ll#0,i#lr#1*i#ll#1))*h_(x#(i#lr#0*i#ll#0,i#lr#1*i#ll#1)) - 
                                    a_(x#(i#lr))*b_(x#(i#ll))*c_(x#(i#ul))*d_(x#(i#ur))*e_(x#(i#ul))*g_(x#(i#lr#0*i#ll#0,i#lr#1*i#ll#1))*h_(x#(i#ur)));
    Eqn_(j + 4) = L1 - Par_(j + 4);
    PAR_(j + 4) = matrix{{submatrix((vars R), 0..43),matrix{Par_(j + 4)}}};
};


--4-leaf 4-cycle networks (10-21)

Topos = {(1, 2, 3, 0), (3, 2, 1, 0), (1, 3, 2, 0), (2, 3, 1, 0), (1, 2, 0, 3), (0, 2, 1, 3), 
         (0, 3, 2, 1), (2, 3, 0, 1), (0, 2, 3, 1), (3, 2, 0, 1), (2, 1, 3, 0), (3, 1, 2, 0)};
     
for j from 0 to 11 do{
    ll = (Topos#j)#0,
    ul = (Topos#j)#1,
    ur = (Topos#j)#2,
    lr = (Topos#j)#3,
    Par_(j + 10) = toList apply(L, i-> a_(x#(i#lr))*b_(x#(i#ll))*c_(x#(i#ul))*d_(x#(i#ur))*f_(x#(i#ll))*g_(x#(i#ll#0*i#ul#0,i#ll#1*i#ul#1))*h_(x#(i#lr)) - 
                                      a_(x#(i#lr))*b_(x#(i#ll))*c_(x#(i#ul))*d_(x#(i#ur))*e_(x#(i#ll))*g_(x#(i#ul))*h_(x#(i#ul#0*i#ur#0,i#ul#1*i#ur#1)));
    Eqn_(j + 10) = L1 - Par_(j + 10);
    PAR_(j + 10) = matrix{{submatrix((vars R), 0..43),matrix{Par_(j + 10)}}};
};

--4-leaf, double triangle networks (22-24)

Topos = {(1, 2, 3, 0), (2, 1, 3, 0), (1, 0, 3, 2)};


for jj from 0 to 2 do{
    ll = (Topos#jj)#0,
    ul = (Topos#jj)#1,
    ur = (Topos#jj)#2,
    lr = (Topos#jj)#3,
    Par_(jj + 22) = toList apply(L,i->
    a_(x#(i#lr))*b_(x#(i#ll))*c_(x#(i#ul))*d_(x#(i#ur))*
    f_(x#(i#ul))*g_(x#(i#lr#0*i#ll#0,i#lr#1*i#ll#1))*h_(x#(i#lr#0*i#ll#0,i#lr#1*i#ll#1))*k_(x#(i#lr))*l_(x#(i#lr#0*i#ll#0,i#lr#1*i#ll#1))  -- f,k present
    +
    a_(x#(i#lr))*b_(x#(i#ll))*c_(x#(i#ul))*d_(x#(i#ur))*
    e_(x#(i#ul))*g_(x#(i#lr#0*i#ll#0,i#lr#1*i#ll#1))*h_(x#(i#ur))*k_(x#(i#lr))*l_(x#(i#lr#0*i#ll#0,i#lr#1*i#ll#1)) --e, k present
    +
    a_(x#(i#lr))*b_(x#(i#ll))*c_(x#(i#ul))*d_(x#(i#ur))*
    f_(x#(i#ul))*g_(x#(i#lr#0*i#ll#0,i#lr#1*i#ll#1))*h_(x#(i#lr#0*i#ll#0,i#lr#1*i#ll#1))*j_(x#(i#lr))*l_(x#(i#ll))  -- f,j present
    +
    a_(x#(i#lr))*b_(x#(i#ll))*c_(x#(i#ul))*d_(x#(i#ur))*
    e_(x#(i#ul))*g_(x#(i#lr#0*i#ll#0,i#lr#1*i#ll#1))*h_(x#(i#ur))*j_(x#(i#lr))*l_(x#(i#ll))); -- e,j present
    Eqn_(jj + 22) = L1 - Par_(jj + 22);
    PAR_(jj + 22) = matrix{{submatrix((vars R), 0..43),matrix{Par_(jj + 22)}}};
};


-------------------------------------------------------------
-------------------------------------------------------------
----Invariants-----------------------------------------------
-------------------------------------------------------------
-------------------------------------------------------------

g1 = q_(0,3,3,0)*q_(1,1,2,2)*q_(2,0,3,1) - q_(0,0,2,2)*q_(1,3,3,1)*q_(2,1,3,0);


g2 = q_(1,3,3,1) - q_(2,1,2,1);


g3 = q_(1,0,2,3)*q_(2,3,1,0)*q_(3,2,0,1) - q_(1,0,1,0)*q_(2,3,2,3)*q_(3,2,0,1) -
     q_(1,0,2,3)*q_(2,3,0,1)*q_(3,2,1,0) + q_(1,0,0,1)*q_(2,3,2,3)*q_(3,2,1,0) +
     q_(1,0,1,0)*q_(2,3,0,1)*q_(3,2,2,3) - q_(1,0,0,1)*q_(2,3,1,0)*q_(3,2,2,3); 

g4 = q_(0,0,1,1)*q_(1,2,1,2)*q_(2,0,2,0)*q_(3,0,0,3) - q_(0,0,1,1)*q_(1,2,0,3)*q_(2,0,2,0)*q_(3,0,1,2) +
     q_(0,0,1,1)*q_(1,0,2,3)*q_(2,2,0,0)*q_(3,0,1,2) - q_(0,0,0,0)*q_(1,0,2,3)*q_(2,2,1,1)*q_(3,0,1,2);
     

g5 = q_(0,0,0,0)*q_(2,0,1,3)*q_(2,1,2,1) - q_(0,0,2,2)*q_(3,0,0,3)*q_(3,2,1,0);


g6 = q_(0,0,2,2)*q_(2,0,3,1)*q_(3,0,0,3) - q_(0,0,3,3)*q_(2,0,0,2)*q_(3,0,2,1); 



-------------------------------------------------------------
-------------------------------------------------------------
----Proof of Lemma 1-----------------------------------------
-------------------------------------------------------------
-------------------------------------------------------------

--We demonstrate that the set of invariants evaluates to zero on the indicated
--network variety and on none of the others indicated network varieties



--Proof of part (ii) for K2P and K3P: an invariant that vanishes on exactly one 
--of the single triangle network varieties (network 4)


for j from 4 to 9 do{
    print(j, sub(g1, PAR_j) == 0)
}


--Proof of part (v) for K2P and K3P: an invariant that vanishes on exactly one 
--of the tree varieties (network 1) and none of the double triangle network varieties.
--This invariant also vanishes on exactly one of the single triangle network varieties (network 4) 
--and none of the double triangle network varieties.


for j in {1, 4, 22, 23, 24} do{
    print(j, sub(g1, PAR_j) == 0)
}

--Proof of part (v) for JC only: a set of invariants that vanishes on exactly one 
--of the tree varieties (network 1) and none of the double triangle network varieties.
--This set of invariants also vanishes on exactly one of the single triangle network varieties (network 4) 
--and none of the double triangle network varieties.


for j in  {1, 4, 22, 23, 24} do{
    print(j, sub(g1, PAR_j) == 0,  sub(g2, PAR_j) == 0 )
}

--Proof of parts (vi) and (vii) for JC, K2P, K3P: an invariant that vanishes on exactly one of the double triangle 
--network varieties (network 22) and on no 4-cyle network variety

for j from 10 to 24 do{
    print(j, sub(g3 , PAR_j) == 0)
}

--Proof of part (vi) and (vii) for JC only: set of invariants that vanishes on exactly one 4-cycle 
--network variety (network 10) and no double triangle network variety

for j from 10 to 24 do{
    print(j, sub(g4, PAR_j) == 0,  sub(g5, PAR_j) == 0)
}

--Proof of part (vi) and (vii) for K2P and K3P: set of invariants that vanishes on exactly one 4-cycle 
--network variety (network 10) and no double triangle network variety

for j from 10 to 24 do{
    print(j, sub(g4, PAR_j) == 0,  sub(g6, PAR_j) == 0)
}


-------------------------------------------------------------
-------------------------------------------------------------
----Proof of Lemma 2-----------------------------------------
-------------------------------------------------------------
-------------------------------------------------------------

--Proof of (i) for JC, K2P, K3P: an invariant that vanishes on a double triangle
--network variety (network 22) but on no variety of a tree or single triangle-network variety
--with a conflicting split.

for j in {2, 3, 5, 6, 7, 8, 22} do{
    print(j, sub(g3, PAR_j) == 0)
}

--Proof of (ii) for JC: an invariant that vanishes on a single triangle network variety (network 4)
--but on no variety of a tree with a conflicting split.
for j in {2, 3, 4} do{
    print(j, sub(g2, PAR_j) == 0)
}

--Proof of (ii) for K2P, K3P: an invariant that vanishes on a single triangle network variety (network 4)
--but on no variety of a tree with a conflicting split.
for j in {2, 3, 4} do{
    print(j, sub(g1, PAR_j) == 0)
}


-------------------------------------------------------------
-------------------------------------------------------------
--Randomized algorithm for finding a subset of the variables
--that will distinguish two networks
-------------------------------------------------------------
-------------------------------------------------------------

--Finds an invariant in the ideal of network n1 but not
--in the ideal of network n2

n1 = 3
n2 = 4
J1 = jacobian matrix{Par_n1}; 
J2 = jacobian matrix{Par_n2}; 


J1 = J1^{0..(#L2 - 1)}; -- exclude parameter columns
J2 = J2^{0..(#L2 - 1)}; -- exclude parameter columns


var = 5 --size of variable subsets to search
iterations = 100 --number of iterations to perform
LL = {} --initialize the subset of variables to the empty set
JJ1 = submatrix(J1, LL);
JJ2 = submatrix(J2, LL);

--A list of random rational numbers to substitute for the parameter values in the Jacobian
RL = matrix{for i from 1 to 44 list random QQ};

--The substitution map for the random parameter values
Msub = matrix{{RL, submatrix((vars R), 44..107)}}; 


--Initialize ranks to zero
JJJ1 = sub(JJ1 , Msub); 
JJJ2 = sub(JJ2 , Msub);
r1 = rank(JJJ1) 
r2 = rank(JJJ2)


--Once a subset of variables S is found, a smaller subset of variables can be found by 
--setting SS = S (and commenting out "SS = 0..(#L - 1);") in the loop below, and running the 
--loop again with a smnaller value of "var."

--This can be repeated to find a small distinguishing subset of variables.

for i from 1 to iterations when r1 >= r2 do {
    --SS = S;
    SS = 0..(#L - 1); 
    LL = {};
    for j from 1 to var do {b = random(#SS), c = SS#b
	, SS = delete(c, SS), LL = append(LL, c)},
    JJ1 = submatrix(J1, LL);
    JJ2 = submatrix(J2, LL);
    JJJ1 = sub(JJ1, Msub);
    JJJ2 = sub(JJ2, Msub);
    r1 = rank(JJJ1);
    r2 = rank(JJJ2);
    print(i);
    for k from 1 to 1 when r1 < r2 do {print("found")};
}

S = LL

--Once a distinguishing subset of variables, S, is found, 
--we search for an invariant that involves only these variables.

j1 = jacobian matrix{(Par_n1)_S}; --construct Jacobians on smaller set of variables
j2 = jacobian matrix{(Par_n2)_S};

rank(j1) < rank(j2) --verify that rank(J1) is less than rank(J2)


E_n1 = (Eqn_n1)_S --restrict to the subset of variables with indices S found above
KK = ideal(E_n1);
time GG = selectInSubring(1, gens gb(KK, SubringLimit => 1)); 
I = ideal(GG);
MG = mingens I;
f = MG_(0,0)

--Check that the invariant vanishes on network n1 variety, 
--but not on network n2 variety. If it vanishes on both, change
--the SubringLimit to find more than one invariant, or,
--continue searching for a smaller subset of variables that distinguishes
-- the networks.

sub(f, PAR_n1) == 0 
sub(f, PAR_n2) == 0 



