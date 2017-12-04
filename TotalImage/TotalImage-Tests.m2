
TEST ///
-- cubics with base locus
-- map is surjective onto PP2
-- restart
-- loadPackage "TotalImage"
PP2=QQ[x,y,z];
baseSystem = deg -> ( R:=ZZ[x,y,z]; f:=random(deg,R); f0:=sub(f, matrix "0, 0 ,1" ); return f-f0*z^deg );
f1=sub(baseSystem(3),PP2);
f2=sub(baseSystem(3),PP2);
f3=sub(baseSystem(3),PP2);
L={f1,f2,f3};
(N,E)=totalImage(L)
assert(length(E) == 0)
-- o = ({ideal ()}, {})
///

TEST ///
-- 'removable' base locus should still be detected
-- restart
-- loadPackage "TotalImage"
PP1 = QQ[x,y];
L = {x^2,x*y}
(N,E) = totalImage(L)
assert(length(E)==1)

-- (1) ideal()
-- (0) |====ideal b_0

-- o = ({ideal (), ideal b }, {{0, 1}})
--                        0
///

TEST ///
-- another 'removable' base locus
-- restart
-- loadPackage "TotalImage"
PP2 = QQ[x,y,z]
L = {x*z,y*z,z*z}
(N,E) = totalImage(L)
assert(length(E)==1)

-- (2) ideal()
-- (1) |====ideal b_2

-- o = ({ideal (), ideal b }, {{0, 1}})
--                        2
///

TEST ///
-- very simple non-trivial example
-- restart
-- loadPackage "TotalImage"
PP2=QQ[x,y,z];
L={z^2,x^2,x*y}
time (N,E)=totalImage(L)
-- totalImage(L,Verbose=>true)
assert(length(E)==2)
assert(sort(N/dim)=={1,2,3})

-- (2) ideal()
-- (1) |====ideal b_1
-- (0) |    |====ideal(b_2,b_1)

-- o = ({ideal (), ideal b , ideal (b , b )}, {{0, 1}, {1, 2}})
--                        1          2   1
///

TEST ///
-- linear system of quadrics with two base points in PP2
-- restart
-- loadPackage "TotalImage"
PP2 = QQ[x,y,z];
L = {x^2+y^2-z^2,x^2+y^2+x*y-z^2,x*y+y^2}
(N,E)=totalImage(L)
assert(sort(N/dim)=={1,2,3})

-- (2) ideal()
-- (1) |====ideal(b_0-b_1+b_2)
-- (0) |    |====ideal(b_2,b_0-b_1)

-- o = ({ideal (), ideal(b  - b  + b ), ideal (b , b  - b )}, {{0, 1}, {1, 2}})
--                        0    1    2           2   0    1
///

TEST ///
-- projection of nodal cubic from node
-- restart
-- loadPackage "TotalImage"
PP2 = QQ[x,y,z];
L = {x,y}
X = ideal "y2z-x3-x2z"
(N,E)=totalImage(L,X)
assert(sort(N/dim) == {1,1,2})

-- (1) ideal()
-- (0) |====ideal(-b_0+b_1)
-- (0) |====ideal(b_0+b_1)

-- o = ({ideal (), ideal(- b  + b ), ideal(b  + b )}, {{0, 1}, {0, 2}})
--                          0    1          0    1
///

TEST ///
-- projection of smooth cubic from point should cover PP1
-- restart
-- loadPackage "TotalImage"
PP2 = QQ[x,y,z];
L = {x,y-z}
-- X = ideal "xy"
X = ideal "y2z-x3-2x2z-z3"
(N,E)=totalImage(L,X)
assert(sort(N/dim) == {2})

///

TEST ///
-- projection of conic onto line misses infinity
-- restart
-- loadPackage "TotalImage"
PP2 = QQ[x,y,z];
L = {y,z}
-- X = ideal "xy"
X = ideal "xy-z2"
(N,E)=totalImage(L,X)
assert(sort(N/dim) == {1,2})

///

TEST ///
-- Cremona
-- restart
-- loadPackage "TotalImage"
PP2 = QQ[x,y,z]
L = {y*z,x*z,x*y}
(N,E)=totalImage(L)
assert(sort(N/dim) == {1,1,1,1,1,1,2,2,2,3})

-- (2) ideal()
-- (1) |====ideal b_2
-- (0) |    |====ideal(b_2,b_0)
-- (0) |    |====ideal(b_2,b_1)
-- (1) |====ideal b_1
-- (0) |    |====ideal(b_1,b_0)
-- (0) |    |====ideal(b_2,b_1)
-- (1) |====ideal b_0
-- (0) |    |====ideal(b_2,b_0)
-- (0) |    |====ideal(b_1,b_0)

-- o4 = ({ideal (), ideal b , ideal b , ideal b , ideal (b , b ), ideal (b , b ), ideal (b , b ), ideal (b , b ), ideal
--                         2         1         0          2   0           2   1           1   0           2   1        
--      ---------------------------------------------------------------------------------------------------------------
--      (b , b ), ideal (b , b )}, {{0, 1}, {0, 2}, {0, 3}, {1, 4}, {1, 5}, {2, 6}, {2, 7}, {3, 8}, {3, 9}})
--        2   0           1   0

///

TEST ///
-- from [EH02] page 182 (Exercise IV-43)
-- the exc. div. isn't a projective space
-- restart
-- loadPackage "TotalImage"
PP2 = QQ[x,y,z]
L = {x^3,x*y*z,y^2*z}
(N,E)=totalImage(L)
assert(sort(N/dim) == {1, 1, 1, 1, 1, 1, 2, 2, 2, 3})
-- above is correct / below is to see a bad test
-- assert(sort(N/dim) == {1, 2, 2, 2, 3})

-- (2) ideal()
-- (1) |====ideal b_2
-- (0) |    |====ideal(b_2,b_1)
-- (0) |    |====ideal(b_2,b_1)
-- (1) |====ideal b_1
-- (0) |    |====ideal(b_2,b_1)
-- (0) |    |====ideal(b_2,b_1)
-- (0) |    |====ideal(b_1,b_0)
-- (1) |====ideal b_0
-- (0) |    |====ideal(b_1,b_0)

-- o4 = ({ideal (), ideal b , ideal b , ideal b , ideal (b , b ), ideal (b , b ), ideal (b , b ), ideal (b , b ), ideal
--                         2         1         0          2   1           2   1           2   1           2   1        
--      ---------------------------------------------------------------------------------------------------------------
--      (b , b ), ideal (b , b )}, {{0, 1}, {0, 2}, {0, 3}, {1, 4}, {1, 5}, {2, 6}, {2, 7}, {2, 8}, {3, 9}})
--        1   0           1   0

///

TEST ///
-- blowup a quadric hypersurface in PPn containing the rational normal curve of degree n
-- restart
-- loadPackage "TotalImage"
n = 4; PPn = QQ[p_0..p_n]; I = minors(2,matrix{{p_0..p_(n-1)},{p_1..p_n}}); L = first entries gens I; X = ideal (p_0*p_3-p_1*p_2);
time (N,E)=totalImage(L,X)
assert(sort(N/dim) =={2, 2, 2, 3, 3, 4})

-- (3) ideal(b_1,b_2*b_3+b_0*b_5)
-- (2) |====ideal(b_1,b_2*b_3+b_0*b_5,b_3*b_4^2-b_2^2*b_5-2*b_2*b_3*b_5-b_3^2*b_5,b_2^3+2*b_2^2*b_3+b_2*b_3^2+b_0*b_4^2)
-- (1) |    |====ideal(b_2,b_1,b_0,b_4^2-b_3*b_5)
-- (1) |    |====ideal(b_4,b_2+b_3,b_1,b_3^2-b_0*b_5)
-- (2) |====ideal(b_2,b_0,b_1)
-- (1) |    |====ideal(b_2,b_1,b_0,b_4^2-b_3*b_5)
     -- used 0.715593 seconds

-- o9 = ({ideal (b , b b  + b b ), ideal (b , b b  + b b , b b  - b b  - 2b b b  - b b , b  + 2b b  + b b  + b b ),
--                1   2 3    0 5           1   2 3    0 5   3 4    2 5     2 3 5    3 5   2     2 3    2 3    0 4  
--      ---------------------------------------------------------------------------------------------------------------
--                                              2                                   2                              2
--      ideal (b , b , b ), ideal (b , b , b , b  - b b ), ideal (b , b  + b , b , b  - b b ), ideal (b , b , b , b  -
--              2   0   1           2   1   0   4    3 5           4   2    3   1   3    0 5           2   1   0   4  
--      ---------------------------------------------------------------------------------------------------------------
--      b b )}, {{0, 1}, {0, 2}, {1, 3}, {1, 4}, {2, 5}})
--       3 5
///


TEST ///
-- restart
-- loadPackage "TotalImage"
n = 5; PPn = QQ[p_0..p_n]; I = minors(2,matrix{{p_0..p_(n-1)},{p_1..p_n}}); L = first entries gens I; X = ideal (p_0*p_3-p_1*p_2);
time (N,E)=totalImage(L,X);
-- time (N,E)=totalImage(L,X,Verbose=>true);
-- time (N,E)=totalImage(L,X,SmarterHyperplanes=>false,Verbose=>true);
assert(sort(N/dim) =={2, 2, 2, 4, 4, 5})
-- time for i from 1 to 10 do totalImage(L,X);
-- time for i from 1 to 10 do totalImage(L,X,SmarterHyperplanes=>true);

-- (4) ideal(b_1,b_5*b_7-b_4*b_8+b_2*b_9,b_5*b_6-b_3*b_8,b_4*b_6-b_3*b_7+b_0*b_9,b_2*b_6+b_0*b_8,b_4^2-b_2*b_5-b_3*b_5-b_2*b_7-b_0*b_9,b_2*b_3+b_0*b_5,b_3*b_4*b_7-b_3^2*b_8+b_0*b_5*b_8+b_0*b_7*b_8-b_0*b_4*b_9-b_0*b_6*b_9,b_3^2*b_7^2-b_3^2*b_6*b_8+b_0*b_6*b_7*b_8+b_0*b_3*b_8^2-b_0*b_6^2*b_9-2*b_0*b_3*b_7*b_9+b_0^2*b_9^2)
-- (3) |====ideal(b_1,-b_5*b_7+b_4*b_8-b_2*b_9,-b_4^2+b_2*b_5+b_3*b_5+b_2*b_7+b_0*b_9,b_2*b_3+b_0*b_5,b_5*b_6-b_3*b_8,b_2*b_6+b_0*b_8,b_4*b_6-b_3*b_7+b_0*b_9,-b_2*b_5^2-b_0*b_8^2+b_2^2*b_9+b_0*b_5*b_9+b_0*b_7*b_9,b_2^3-b_0*b_2*b_5+b_0*b_2*b_7+b_0^2*b_9,-b_2*b_4*b_5+b_2^2*b_8-b_0*b_5*b_8+b_0*b_4*b_9,b_5^3-b_5^2*b_7+b_2*b_8^2+b_4^2*b_9-3*b_2*b_5*b_9-b_2*b_7*b_9,-b_2^2*b_4-b_0*b_4*b_7+b_0*b_2*b_8+b_0*b_3*b_8,b_5^2*b_7-b_2*b_8^2-b_3*b_8^2+b_2*b_5*b_9+b_3*b_7*b_9-b_0*b_9^2,-b_2^2*b_5+b_0*b_5^2-b_0*b_5*b_7+b_0*b_3*b_9,b_4*b_5^2-b_4*b_5*b_7+b_2*b_7*b_8-b_2*b_4*b_9+b_3*b_4*b_9+b_0*b_8*b_9,b_2*b_4*b_5-b_3*b_4*b_7+b_3^2*b_8-b_0*b_5*b_8,b_4^2*b_5+b_2*b_5^2-b_4^2*b_7+b_2*b_7^2+b_0*b_8^2-b_2^2*b_9+b_3^2*b_9-2*b_0*b_5*b_9,-b_2^2*b_5-b_2^2*b_7-b_0*b_7^2+b_0*b_6*b_8+b_0*b_2*b_9,b_5^2*b_8-b_6*b_8^2+b_6*b_7*b_9-b_2*b_8*b_9+b_3*b_8*b_9,b_2*b_5^2+b_2*b_5*b_7-b_3*b_7^2+b_3*b_6*b_8-b_0*b_5*b_9,b_4*b_5*b_7-b_2*b_7*b_8-b_3*b_7*b_8+b_2*b_4*b_9+b_3*b_6*b_9-b_0*b_8*b_9,-b_6*b_7^2+b_2*b_5*b_8+b_6^2*b_8+b_2*b_7*b_8-b_0*b_8*b_9,-b_6*b_7*b_8+b_2*b_8^2+b_3*b_8^2+b_6^2*b_9)
-- (1) |    |====ideal(b_8,b_6,b_5+b_7,b_4,b_2+b_3,b_1,b_7^2+b_3*b_9,b_3*b_7-b_0*b_9,b_3^2+b_0*b_7)
-- (1) |    |====ideal(b_5,b_4,b_3,b_2,b_1,b_0,b_8^2-b_7*b_9,b_7*b_8-b_6*b_9,b_7^2-b_6*b_8)
-- (3) |====ideal(b_5,b_2,b_0,b_4,b_3,b_1)
-- (1) |    |====ideal(b_5,b_4,b_3,b_2,b_1,b_0,b_8^2-b_7*b_9,b_7*b_8-b_6*b_9,b_7^2-b_6*b_8)
     -- used 2.41834 seconds

-- output too long
///

TEST ///
-- Maple example
-- restart
-- loadPackage "TotalImage"
R = QQ[u,v,t]
L = {u*v,u*t,v^2,t^2}
(N,E)=totalImage(L)
assert(sort(N/dim) =={2, 3})

-- (2) ideal(b_1^2*b_2-b_0^2*b_3)
-- (1) |====ideal(b_3,b_2)

--               2      2
-- o4 = ({ideal(b b  - b b ), ideal (b , b )}, {{0, 1}})
--               1 2    0 3           3   2
///

TEST ///
-- domain is singular
-- project singular cone from singularity to plane
-- surjective
-- restart
-- loadPackage "TotalImage"
PP3 = QQ[x,y,z,w]
X = ideal "xy-z2"
L = {x,y,z}
(N,E)=totalImage(L,X)
assert(sort(N/dim) =={2})

-- (1) ideal(b_0*b_1-b_2^2)

--                      2
-- o6 = ({ideal(b b  - b )}, {})
--               0 1    2
///

TEST ///
-- THIS TEST IS SLOWWW
-- about 200secs CPU time on a 2017 MacBook Pro

-- restart
-- loadPackage "TotalImage"
-- PP2 = QQ[x,y,z]
-- L = {x^6*y^2*z+4*x^5*y^3*z+5*x^4*y^4*z+2*x^3*y^5*z+x^6*y*z^2+14*x^5*y^2*z^2+36*x^4*y^3*z^2+27*x^3*y^4*z^2+4*x^2*y^5*z^2+4*x^5*y*z^3+36*x^4*y^2*z^3+56*x^3*y^3*z^3+14*x^2*y^4*z^3+5*x^4*y*z^4+27*x^3*y^2*z^4+14*x^2*y^3*z^4+2*x^3*y*z^5+4*x^2*y^2*z^5, 2*x^5*y^3*z+5*x^4*y^4*z+4*x^3*y^5*z+x^2*y^6*z+4*x^5*y^2*z^2+27*x^4*y^3*z^2+36*x^3*y^4*z^2+14*x^2*y^5*z^2+x*y^6*z^2+14*x^4*y^2*z^3+56*x^3*y^3*z^3+36*x^2*y^4*z^3+4*x*y^5*z^3+14*x^3*y^2*z^4+27*x^2*y^3*z^4+5*x*y^4*z^4+4*x^2*y^2*z^5+2*x*y^3*z^5, 4*x^5*y^2*z^2+14*x^4*y^3*z^2+14*x^3*y^4*z^2+4*x^2*y^5*z^2+2*x^5*y*z^3+27*x^4*y^2*z^3+56*x^3*y^3*z^3+27*x^2*y^4*z^3+2*x*y^5*z^3+5*x^4*y*z^4+36*x^3*y^2*z^4+36*x^2*y^3*z^4+5*x*y^4*z^4+4*x^3*y*z^5+14*x^2*y^2*z^5+4*x*y^3*z^5+x^2*y*z^6+x*y^2*z^6}
-- time (N,E)=totalImage(L,Verbose=>true);
-- -- time (N,E)=totalImage(L,Verbose=>true,SmarterHyperplanes=>false);
-- assert(sort(N/dim) =={2})
///

TEST ///
-- restart
-- loadPackage "TotalImage"
PP2 = QQ[x,y,z]
f1=random(3,PP2);
f2=random(3,PP2);
f3=random(3,PP2);
f1=(f1-z^3*coefficient(z^3,f1)-y^3*coefficient(y^3 ,f1)-x^3*coefficient(x^3 ,f1));
f2=(f2-z^3*coefficient(z^3,f2)-y^3*coefficient(y^3 ,f2)-x^3*coefficient(x^3 ,f2));
f3=(f3-z^3*coefficient(z^3,f3)-y^3*coefficient(y^3 ,f3)-x^3*coefficient(x^3 ,f3));
L={f1,f2,f3};
time (N,E)=totalImage(L)
assert(sort(N/dim) =={3})

-- (2) ideal()
     -- used 0.686236 seconds

-- o10 = ({ideal ()}, {})
///

TEST ///
-- restart
-- loadPackage "TotalImage"
PP2 = QQ[x,y,z]
L = {y*z*(2*x+y+z),x*z*(x+2*y+z),x*y*(x+y+2*z)}
-- time for i from 1 to 10 do totalImage(L);
-- time for i from 1 to 10 do totalImage(L,SmarterHyperplanes=>true);
time (N,E)=totalImage(L)
-- time (N,E)=totalImage(L,SmarterHyperplanes=>true)

-- (2) ideal()
--      -- used 0.727898 seconds

-- o5 = ({ideal ()}, {})
///