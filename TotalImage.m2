newPackage(
    "TotalImage",
    Version => "0.2",
    Date => "November 30, 2017",
    Authors => {
        {Name => "Corey Harris", Email => "harris@mis.mpg.de", HomePage => "http://coreyharris.name"},
        {Name => "Mateusz Michalek", Email => "wajcha2@pocztal.onet.pl", HomePage => "http://personal-homepages.mis.mpg.de/michalek/"},
        {Name => "Emre Sertoz", Email => "emresertoz@gmail.com", HomePage => "https://emresertoz.com/"}
    },
    Headline => "A package for computing the image of a rational map as a constructible set",
    AuxiliaryFiles => false
)

export { 
    -- main functions
    "partialImage",
    "outputTree",
    "totalImage",
    "isClosed",
    -- option symbols
    "Clean",
    "Affine",
    "pd",
    "Tries"
}

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

-------------------------------------------
--
-- Main functions
--
-------------------------------------------

--EXPORTED
partialImage = method(Options => {Verbose => false, Verify => true, pd => true, Tries => 5})
partialImage List := opts -> (L) -> (
    partialImage(L,sub(ideal 0,ring L#0),opts)
 )
partialImage (List,Ideal) := opts -> (L,X) -> (
    T:=generateTarget(L,X);
    partialImage(L,X,T,opts)
)
partialImage (List,Ideal,Ring) := opts -> (L,X,T) -> (
    -- L: list of polynomials defining a rational map f
    -- X: ideal of a variety in P^M   
    -- T: coordinate ring of target projective space
    -- OUTPUT: (image(f), divisors in complement of image of f on X \ B)
    R := ring X;
    targetPPm := T;
    f := map(R,targetPPm,L);
    if opts.Verbose then << "helper function partialImage initiated..." << endl;
    if opts.Verbose then << "(domain has dim " << dim variety X << ")" <<  endl;
    imageX := preimage_f X;
    if opts.Verbose then << "computed image" << endl;
    if opts.Verbose then << imageX << endl;
    if opts.Verbose then << "(image has dim " << dim variety imageX << ")" <<  endl;
    baseLocus := ideal L;
    if dim baseLocus < 1 then (
        if opts.pd then (
            return (imageX,{});
        ) else (
            return (imageX,sub(ideal(1),ring imageX));
        );
    );
    dimageX := dim imageX;
    if opts.Verbose then << "(image has dim " << dim variety imageX << ")" <<  endl;
    fiberDim := dim X - dimageX;
    shrinkX := () -> (
        binomialMap := () -> (
           N := numgens R;
           n := N - fiberDim;
           firstVars := take(gens R,n);
           l := flatten for i from 1 to (N//n+1) list (
               for v in firstVars list (v)
               );
           rndVarList := random(take(l,N));
           R' := (coefficientRing R)(monoid[firstVars]);
           restrict := map(R',R,rndVarList / (i -> sub(i,R')));
           restrictedX := restrict(X);
           fRestricted := map(R',targetPPm, L / (i -> restrict(i)));
           restrictedImage := preimage_fRestricted(restrictedX);
           return (fRestricted,restrict,restrictedX,restrictedImage)
        );
        advBinomialMap := () -> (
           N := numgens R;
           n := N - fiberDim;
           firstVars := take(gens R,n);
           l := flatten for i from 1 to (N//n+1) list (
               for v in firstVars list (rand(5)*v)
               );
           rndVarList := random(take(l,N));
           R' := (coefficientRing R)(monoid[firstVars]);
           restrict := map(R',R,rndVarList / (i -> sub(i,R')));
           restrictedX := restrict(X);
           fRestricted := map(R',targetPPm, L / (i -> restrict(i)));
           restrictedImage := preimage_fRestricted(restrictedX);
           return (fRestricted,restrict,restrictedX,restrictedImage)
        );
        monomialMap := () -> (
           N := numgens R;
           n := N - fiberDim;
           keepVars := take(random(gens R),n);
           rndVarList := random (keepVars | for i from 1 to fiberDim list 0);
           R' := (coefficientRing R)(monoid[keepVars]);
           restrict := map(R',R,rndVarList / (i -> sub(i,R')));
           restrictedX := restrict(X);
           fRestricted := map(R',targetPPm, L / (i -> restrict(i)));
           restrictedImage := preimage_fRestricted(restrictedX);
           return (fRestricted,restrict,restrictedX,restrictedImage)
        );

        TRIES := opts.Tries;
        -- look for very simple linear spaces
        (fRestricted,r,restrictedX,restrictedImage) := monomialMap();
        for i from 1 to TRIES do (
            if dim(restrictedX)==dimageX and isSubset(restrictedImage,imageX) then (
                if opts.Verbose == true then print("#" | toString i | ": Found a good monomial one!");
                return (fRestricted,r,restrictedX)
            );
            (fRestricted,r,restrictedX,restrictedImage) = monomialMap();
        );

        -- slightly more complicated
        (fRestricted,r,restrictedX,restrictedImage) = binomialMap();
        for i from 1 to TRIES do (
            if dim(restrictedX)==dimageX and isSubset(restrictedImage,imageX) then (
                if opts.Verbose == true then print("#" | toString i | ": Found a good binomial one!");
                return (fRestricted,r,restrictedX)
            );
            (fRestricted,r,restrictedX,restrictedImage) = binomialMap();
        );

        -- add nontrivial coefficients
        (fRestricted,r,restrictedX,restrictedImage) = advBinomialMap();
        for i from 1 to TRIES do (
            if dim(restrictedX)==dimageX and isSubset(restrictedImage,imageX) then (
                if opts.Verbose == true then print("#" | toString i | ": Found a good advBinomial one!");
                return (fRestricted,r,restrictedX)
            );
            (fRestricted,r,restrictedX,restrictedImage) = advBinomialMap();
        );

        -- give up and look for random hyperplanes
        r = hyperplaneSection(X,fiberDim);
        restrictedX = r(X);
        fRestricted =  map(ring restrictedX, targetPPm, L / (i -> r(i)));
        restrictedImage = preimage_fRestricted(restrictedX);
        for i from 1 to TRIES do (
            if dim(restrictedX)==dimageX and isSubset(restrictedImage,imageX) then (
                if opts.Verbose == true then print("#" | toString i | ": Found a good random one!");
                return (fRestricted,r,restrictedX)
            );
            r = hyperplaneSection(X,fiberDim);
            restrictedX = r(X);
            fRestricted =  map(ring restrictedX, targetPPm, L / (i -> r(i)));
            restrictedImage = preimage_fRestricted(restrictedX);
        );
        print("dim X: " | dim X | "  dim restrictedX: " | dim restrictedX | "  dim imageX: " | dimageX);
        error "couldn't find a hyperplane after many tries!";
    );   
    if opts.Verify == true then (
        r := "restriction map";
        (f,r,X) = shrinkX();
        R = ring X;
        baseLocus = r(ideal L);
    ) else (
        hyperIncl := hyperplaneSection(X,fiberDim);
        baseLocus = hyperIncl(ideal L);
        -- now we move to the linear subspace
        X = hyperIncl(X);
        if opts.Verbose then << "moved to linear subspace" << endl;
        R = ring X;
        f = map(R,targetPPm,L / (i -> hyperIncl(i)));
    );
    if dim (X+baseLocus) < 1 then (
        if opts.pd then (
            return (imageX,{});
        ) else (
            return (imageX,sub(ideal(1),ring imageX));
        );
    );
    if opts.Verbose then << "getting ready to compute blowup" << endl;
    Bl := blowup(baseLocus); -- blowup of PPk (hyperplane);
    BlRing := quotient Bl;
    if opts.Verbose then << "computed blowup of PPn" << endl;
    gens1 := take(gens ring Bl, numgens R);
    gens2 := drop(gens ring Bl, numgens R);
    pr1 := map(BlRing,R,sub(gens R, ring Bl));
    pr2 := map(BlRing,targetPPm,sub(gens targetPPm, ring Bl));
    properX := sub(ideal 0, BlRing);
    if (X != sub(ideal 0,ring X)) then (
        if opts.Verbose then << "X was not 0!" << endl;
        properX = saturate(pr1(X),pr1(baseLocus));
    );
    if opts.Verbose then << "computed blowup of X" << endl;
    E := pr1(baseLocus) + properX;
    if opts.Verbose then << "computed exc divisor" << endl;
    E = saturate(E,ideal sub(gens2,BlRing));
    if opts.Verbose then << "saturating with respect to domain variables" << endl;
    E = saturate(E,ideal sub(gens1,BlRing));
    if opts.Verbose then << "saturating with respect to codomain variables" << endl;
    E = sub(E,ring Bl) + Bl;
    if opts.Verbose then << "restricted E to Bl" << endl;
    imageE := sub(eliminate(E,gens1),targetPPm);
    if opts.Verbose then << "computed image of E" << endl;
    if dim imageE < 1 then (
        if opts.pd then (
            return (imageX, {})
        ) else (
            return (imageX, sub(ideal(1),ring imageX))
        );
    );
    ImageXRing := quotient imageX;
    if opts.pd then (
        if opts.Verbose then << "computing components of image of E" << endl;
        -- print("pd true");
        pdE := minimalPrimes imageE;
        if opts.Verbose then << netList(pdE) << endl << endl;
        return (imageX, pdE)
    ) else (
        -- print("pd false");
        if opts.Verbose then << endl;
        return (imageX, imageE)
    );
)

isClosed = method(Options => {Verbose => false,Tries=>10})
isClosed List := opts -> L -> (
    isClosed(L,sub(ideal 0,ring L#0),opts)
)
isClosed(List,Ideal) := opts -> (L,X) -> (
    (imageX, imageE) := partialImage(L,X,pd=>false,Verbose=>opts.Verbose);
    R := ring X;
    T := ring imageX;
    f := map(R,T,L);
    dimageE := dim imageE;
    pullback := f(imageE)+X;
    imageOfPullback := preimage_f( pullback );
    dimageOfPullback := dim imageOfPullback;
    if ( dimageE != dimageOfPullback ) then (return false);
    if opts.Verbose then print("Decomposing image of exceptional divisor");
    pdE := minimalPrimes(imageE);
    if opts.Verbose then << netList(pdE) << endl << endl;
    for p in pdE do ( 
        -- print(p);
        -- print(f(p)+X);
        if not isClosed(L,saturate(f(p)+X,ideal L),opts) then return false ;
    );
    return true
)

treeBuilder = method(Options => {Verbose => false,Verify=>false,Tries=>10})
treeBuilder List := opts -> L -> (
    treeBuilder(L,sub(ideal 0,ring L#0),opts)
)
treeBuilder (List,Ideal) := opts -> (L,X) -> (
  -- contains the domain and preimages of exceptional images (minus the base locus)

  -- each domain produces a "fin"
  -- we store the index to which this fin is to be attached
  -- within the tree. Negative index means root.
  domains:={(X,-1)};

  -- the tree of images and exceptional images
  nodes := {}; 
  edges := {};

  -- temporary variables to loop with
  i:="void";
  D:="void";
  zariskiImage:="void";
  exceptionalLoci:="void";
  exceptionalDomi:="void";
  newEdges:="void";

  -- we create the coordinate ring of the target PPm
  -- and use it for all partialImage function calls
  T:=generateTarget(L,X);

  for j when (j < #domains) do (

    D := domains#j;

    -- index of domain
    i =  D#1;

    (zariskiImage,exceptionalLoci)=partialImage(L,D#0,T,opts);

    exceptionalDomi = apply(exceptionalLoci,E -> componentsOfPullback(L,X,E));

    -- index the exceptional domains
    exceptionalDomi = for j when (j < #exceptionalDomi) list (
      for Z in exceptionalDomi#j list (Z,#nodes+j+1)
    );

    domains=domains | flatten(exceptionalDomi);

    -- if computations are done in parallel
    -- the following steps need to be completed without
    -- interruption for the indexing to be correct
    if (i !=-1) then (
      edges=append(edges,{i,#nodes});
    );
    newEdges = for k from 1 to #exceptionalLoci list {#nodes , #nodes + k};
    edges=edges | newEdges;
    nodes=append(nodes,zariskiImage);
    nodes=nodes | exceptionalLoci;
    );
  
  return (nodes,edges);
)


--EXPORTED
outputTree = (N,E) -> (
    lvl := 0;   
    (C,P) := childrenAndParents(N,E);
    << endl;
    
    printChildren := (node,childList,lvl) -> (
        indentation := "(" | toString(dim(variety(N#node))) | ") ";
        -- indentation := "";
        if lvl > 0 then (
            if lvl % 2 == 0 then (
                indentation = indentation | ((lvl-1)* "|    ") | "|==(+)=="
            ) else (
                indentation = indentation | ((lvl-1)* "|    ") | "|==(-)=="
            );
        );
        print(indentation|toString N#node);
        for c in childList do printChildren(c,C#c,lvl+1);
    );
    
    printChildren(0,C#0,0);
)

--EXPORTED
totalImage = method(Options => {Verbose => false, Clean => true, Verify => true, Affine => false,Tries => 10})
totalImage List := opts -> L -> (
    totalImage(L,sub(ideal 0,ring L#0),opts)
)
totalImage (List,Ideal) := opts -> (L,X) -> (
    if opts.Affine or not all(L , isHomogeneous) or not all(L, f -> degree(first L)==degree f) then (
        ourR := (coefficientRing ring X)(monoid[{getSymbol("zhom")}| for v in gens ring X list getSymbol toString v]);
        maxDegree := max(for f in L list first degree f);
        L = {ourR_0^(maxDegree+1)} | for f in L list homogenizeD(sub(f,ourR),ourR_0,maxDegree+1);
        X = sub(X,ourR);
    );
    tree:=treeBuilder(L,X,Verbose=>opts.Verbose,Verify=>opts.Verify,Tries=>opts.Tries);
    if opts.Clean then (
        tree=reindexTree(removeDuplicates(tree));
        tree=reindexTree(cleanTree(tree));
    );
    outputTree(tree);
    return tree;
)


affineTotalImage = method(Options => {Verbose => false, Clean => true})
affineTotalImage List := opts -> L -> (
    affineTotalImage(L,sub(ideal 0,ring L#0),opts)
)
affineTotalImage (List,Ideal) := opts -> (L,X) -> (
    ourR := (coefficientRing ring X)(monoid[{getSymbol("zhom")}| for v in gens ring X list getSymbol toString v]);
    maxDegree := max(for f in L list first degree f);
    newL := {ourR_0^(maxDegree+1)} | for f in L list homogenizeD(sub(f,ourR),ourR_0,maxDegree+1);
    totalImage(newL,sub(X,ourR));
)

-------------------------------------------
--
-- Auxilliary Functions
--
-------------------------------------------

-- load(TotalImage#"source directory" | "TotalImage/ImageTrees.m2")

childrenAndParents = (N,E) -> (

  C := for i from 0 to #N-1 list (
        for e in E list if e#0 == i then e#1 else continue
  );

  P := for i from 0 to #N-1 list (
        for e in E list if e#1 == i then e#0 else continue
  );

  return (C,P);
)

childrenAndParentFunctions = (N,E) -> (

  (C,P) := childrenAndParents(N,E);

  getChildren := x -> C#x;
  getChild := x -> if #(C#x) != 1 then error "no unique child" else return (C#x)#0;
  getParent := x -> if x == 0 then error "root has no parent" else return (P#x)#0;

  return (getChildren, getChild, getParent);

)

treeLevels = (N,E) -> (
  levels := {{0}};
  allChildren := {};
  loop := true;
  children:=(childrenAndParentFunctions(N,E))#0;

  while loop do (
    deepestLevel := last(levels);
    allChildren = {};
    for node in deepestLevel do (
      allChildren = allChildren | children(node);
    );

    if allChildren == {} then (loop = false)
    else (levels = append(levels,allChildren))
  );

return levels;
)

-- given and edge e={i,j} removes the verticies i and j
-- and connects the parent of i to all children of j

removeEdge = (N,E,e) -> (
  i := e#0; j := e#1;
  (cc,c,p):=childrenAndParentFunctions(N,E);
  for f in E do (if (member(j,f) or member(i,f)) then E=delete(f,E););
  l := for x in cc(j) list {p(i),x};
  E = E | l;
  return (N,E);
);

-- checks if the node i and any one of its children are equal, returns the index of duplicate child
detectDuplicate = (N,E,i) -> (
  (C,P) := childrenAndParents(N,E);
  children := C#i;
  for j in children do (
      if (N#i == N#j) then return (true,j) else continue
  );
  return (false,-1);
);

-- gets the subtree with root i
subTree = (N,E,i) -> (
  nodes:=toList(0..(#N-1));
  (children,c,p):=childrenAndParentFunctions(N,E);
  descendants:={i};

  -- finds all nodes which descend from i
  for j when (j < #descendants) do (
    descendants = descendants | children(descendants#j);
    );
  descendants=sort(descendants);

  E' := for e in E list ( if member(e#0,descendants) then e else continue );

  f := l -> if member(l,descendants) then #select(nodes,j->((not member(j,descendants)) and j < l)) else error (toString(l)|" is not a descendant of "|toString(i));

  newN := for i in descendants list N#i;
  newE := apply(E',e->{e#0-f(e#0),e#1-f(e#1)});

  return (newN,newE)
)


-- assumption: nodes at odd depth are strictly smaller than their parents

removeDuplicates = (N,E) -> (
  l := treeLevels(N,E);
  ll := for i when (2*i+1 < #l) list (l#(2*i+1));
  ll = flatten(ll);
  duplicate := "dummy variable";

  badEdges := for x in ll list (
    duplicate := detectDuplicate(N,E,x);
    if duplicate#0 then {x,duplicate#1} else continue
  );
  
  for e in badEdges do E = (removeEdge(N,E,e))#1;

  --some children (and their descendants) are left hanging, we clean them with subTree
  return subTree(N,E,0);
);

getLeaves = (N,E) -> (
   (C,P) := childrenAndParents(N,E);
   return for i from 0 to #N-1 list ( 
      if C#i == {} and P#i != {} then i else continue
   );
)

pruneLeaves = (N,E) -> (
    leaves := getLeaves(N,E);
    emptyLeaves := select(leaves,l -> (dim N#l < 1));
    newEdges := select(E,e -> not member(e#1,emptyLeaves));
    return (N,newEdges)
)

cleanTree = (N',E') -> (
    (N,E) := pruneLeaves(N',E');
    (C,P) := childrenAndParents(N,E);
    L := getLeaves(N,E);

    badLeaves := for l in L list (
      if (dim N#(P#l#0) == dim (N#l))
        then l
      else continue);

    badEdges1 := for l in badLeaves list {P#l#0,l};
    badEdges2 := for l in badLeaves list (
      p := P#l#0; {P#p#0,p}
    );
    badEdges := badEdges1 | badEdges2;

    newEdges := select(E,e-> not member(e,badEdges));

    if E != newEdges then 
      return cleanTree(N,newEdges)
    else return (N,E)
)

ZZ * String := (z,s) -> (
    if z == 0 then return "";
    return fold((i,j) -> i|j, (1..z) / (x -> s))
)

-- removes nodes that no longer belong to the tree
-- reindexes the edges accordingly
reindexTree = (N,E) -> (

  nodes:=toList(0..(#N-1));
  (C,P):=childrenAndParents(N,E);

  -- 0 being the root is always "live" so we skip it
  deadNodes := for i from 1 to #N-1 list (
    if P#i == {} then i else continue
  );

  liveNodes := select(nodes,i->not member(i,deadNodes));

  -- reindexing by f
  f := i -> if member(i,deadNodes) then error("should be a live node") else return #select(nodes,j->(member(j,deadNodes) and j < i));

  newN := for i in liveNodes list N#i;
  newE := apply(E,e->{e#0-f(e#0),e#1-f(e#1)});

  return (newN,newE);
)
sub (List,Ring) := (l,R) -> (l/ (i -> sub(i,R)));

removeRedundantGenerators = (D,R) -> (
    return sub(trim radical sub(D,R),ring D)
)

homogenizeD = (f,x,d) -> (homogenize(f,x)*x^(d-first(degree(f))));

pullback = (L,X,excImage) -> (
    f := map(ring L#0,ring excImage, L);
    D := sub(excImage,source f);
    return radical(saturate(f(D)+X,ideal L));
)

componentsOfPullback = (L,X,excImage) -> (
    f := map(ring L#0,ring excImage, L);
    D := sub(excImage,source f);
    return minimalPrimes(saturate(f(D)+X,ideal L));
)


generateTarget = (L,X) -> (
    R := ring X;
    m := #L - 1;
    C := coefficientRing R;
    return C(monoid[(0..m) / (i -> (getSymbol "b")_i)])
)

hyperplaneSection = (X,n) -> (
    -- Returns a random hyperplane section of X
    -- In a ring corresponding to the hyperplane
    R := ring X;    
    N := numgens R;
    firstvars := take(gens R,n);
    lastvars := drop(gens R,n);
    sublist := firstvars / (v -> sum(lastvars / (tt -> random(-200,200)*tt)));
    R' := (coefficientRing R)(monoid[lastvars]);
    return map(R',R,(sublist|lastvars) / (i -> sub(i,R')))
)

rand = (z) -> (
    ps := toList(-z..z);
    return ps_(random(0,length(ps)-1))
)

blowup = method(TypicalValue => Ideal, Options => {Verbose => false})
blowup Ideal := opts -> I -> (
    if opts.Verbose then << 0 << endl;
    r := numgens I;
    S := ring I;
    n := numgens S;
    K := coefficientRing S;
    if opts.Verbose then << 1 << endl;
    tR := K(monoid[getSymbol"t", gens S, (0..r-1) / ( i -> (getSymbol "b")_i ), MonomialOrder => Eliminate 1]);
    if opts.Verbose then << 2 << endl;
    f := map(tR, S, submatrix(vars tR, {1..n}));
    if opts.Verbose then << 3 << endl;
    F := f(gens I);
    if opts.Verbose then << 4 << endl;
    J := ideal apply(1..r, j -> (gens tR)_(n+j)-tR_0*F_(0,(j-1)));
    if opts.Verbose then << 5 << endl;
    L := ideal selectInSubring(1, gens gb J);
    if opts.Verbose then << 6 << endl;
    R := K(monoid[drop(gens tR,1)]);
    g := map(R, tR, 0 | vars R);
    if opts.Verbose then << 7 << endl;
    return trim g(L)
)

beginDocumentation()

-- load(TotalImage#"source directory" | "TotalImage/TotalImage-Doc.m2");

multidoc ///
    Node
        Key
            TotalImage
        Headline
            A package for computing the image of a rational map as a constructible set
        Description
            Text
                Here is where the main summary of our work goes
    Node
        Key
            partialImage
            (partialImage,List)
            (partialImage,List,Ideal)
            (partialImage,List,Ideal,Ring)
        Headline
            Computes the closed image of a rational map to projective space along with the divisors along which the image MAY NOT be closed
        Usage
            partialImage(L)
            partialImage(L,X)
            partialImage(L,X,R)
        Inputs
            L: List 
                list of polynomials defining rational map to $P$^k
            X: Ideal
                source of the rational map
            R: Ring
                ring of the target projective space
        Outputs
            Y: Ideal
                the scheme-theoretic image of X under the rational map defined by L
            Divisors: List
                the divisors in the complement of the (partial) image of X minus base locus
                
        Description
            Text
            Example
                PP2 = QQ[x,y,z]
                L = {y*z,x*z,x*y}
                partialImage(L)
                (Y,Divisors)=partialImage(L)
    Node
        Key
            totalImage
            (totalImage,List)
            (totalImage,List,Ideal)
        Headline
            Computes the constructible set which is the actual image of a rational map on X minus its base locus
        Usage
            totalImage(L)
            totalImage(L,X)
        Inputs
            L: List 
                list of polynomials defining rational map to $P$^k
            X: Ideal
                source of the rational map
        Outputs
            N: List
                nodes in the image tree
            E: List
                edges in the image tree
        Description
            Text
                If the polynomials are not all homogeneous of the same degree, then totalImage will automatically homogenize into a system that defines a rational map with the same image tree.  The result will be an image tree in projective space, with one divisor corresponding to the hyperplane at infinity.
            Text
                First, we compute the image of the Cremona transformation sending $[x,y,z] \mapsto [yz,xz,xy]$.
            Example
                PP2 = QQ[x,y,z]
                L = {y*z,x*z,x*y}
                (N,E)=totalImage(L)
            Text
                Now a more interesting example.  We let X be a quadric surface defined by the vanishing of a $2 \times 2$-minor of the $2 \times n$-matrix seen below.  The map defined by all minors has base locus the rational normal curve.
            Example
                PP4 = QQ[p_0..p_4]; 
                I = minors(2,matrix{{p_0..p_3},{p_1..p_4}})
                L = first entries gens I 
                X = ideal (p_0*p_3-p_1*p_2);
                (N,E)=totalImage(L,X)
    Node
        Key
            outputTree
        Headline
            Prints an image tree, given nodes and edges
        Usage
            outputTree(N,E)
        Inputs
            N: List
            E: List
        Description
            Text
                Given the output of totalImage, outputTree prints the tree in a more human-readable format.  The integers on the left are dimensions.
            Example
                PP4 = QQ[p_0..p_4]; 
                I = minors(2,matrix{{p_0..p_3},{p_1..p_4}})
                L = first entries gens I 
                X = ideal (p_0*p_3-p_1*p_2);
                (N,E)=totalImage(L,X)
                outputTree(N,E)
    Node
        Key
            [totalImage,Affine]
            Affine
        Headline
            Treat map as an affine map (this is automatic if the polynomials are not all of the same degree)
    Node
        Key
            [totalImage,Clean]
            Clean
        Headline
            Option to disable cleaning of the image tree
    Node
        Key
            [partialImage,Verbose]
            [totalImage,Verbose]
    Node
        Key
            [partialImage,Verify]
            [totalImage,Verify]
///

-- load(TotalImage#"source directory" | "TotalImage/TotalImage-Tests.m2");

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
assert(isClosed(L))
assert(isClosed(L,X))
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
restart
loadPackage "TotalImage"
PP2 = QQ[x,y,z]
L = {y*z,x*z,x*y}
(N,E)=totalImage(L)
assert(not isClosed(L))
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
assert(not isClosed(L))
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
assert(not isClosed(L))
assert(not isClosed(L,X))
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

end

restart
loadPackage "TotalImage"
check "TotalImage"
