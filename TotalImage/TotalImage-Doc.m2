
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
