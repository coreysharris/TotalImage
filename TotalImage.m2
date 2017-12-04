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
    AuxiliaryFiles => true
)

export { 
    -- main functions
    "partialImage",
    "outputTree",
    "totalImage",
    -- option symbols
    "Clean",
    "Affine"
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
partialImage = method(Options => {Verbose => false, Verify => false})
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
    baseLocus := ideal L;
    if dim baseLocus < 1 then return (imageX,{});
    dimageX := dim imageX;
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

        TRIES := 4;
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
        if dim baseLocus < 1 then return (imageX,{});
    ) else (
        hyperIncl := hyperplaneSection(X,fiberDim);
        baseLocus = hyperIncl(ideal L);
        if dim baseLocus < 1 then return (imageX,{});
        -- now we move to the linear subspace
        X = hyperIncl(X);
        if opts.Verbose then << "moved to linear subspace" << endl;
        R = ring X;
        f = map(R,targetPPm,L / (i -> hyperIncl(i)));
    );
    if opts.Verbose then << "computing preimage of X" << endl;
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
        return (imageX, {})
    );
    ImageXRing := quotient imageX;
    if opts.Verbose then << "computing components of image of E" << endl << endl;
    pdE := minimalPrimes imageE;
    return (imageX, pdE)
)

treeBuilder = method(Options => {Verbose => false,Verify=>false})
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
            indentation = indentation | ((lvl-1)* "|    ") | "|===="
        );
        print(indentation|toString N#node);
        for c in childList do printChildren(c,C#c,lvl+1);
    );
    
    printChildren(0,C#0,0);
)

--EXPORTED
totalImage = method(Options => {Verbose => false, Clean => true, Verify => true, Affine => false})
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
    tree:=treeBuilder(L,X,Verbose=>opts.Verbose,Verify=>opts.Verify);
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

load(TotalImage#"source directory" | "TotalImage/ImageTrees.m2")

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

load(TotalImage#"source directory" | "TotalImage/TotalImage-Doc.m2");


load(TotalImage#"source directory" | "TotalImage/TotalImage-Tests.m2");

end

restart
loadPackage "TotalImage"
check "TotalImage"
