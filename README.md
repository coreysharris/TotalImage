# TotalImage

## First steps

Clone the git repository and go into the new directory:

```
> git clone https://github.com/coreysharris/TotalImage.git && cd TotalImage
```

Run Macaulay2 from this folder:

```
> M2
```

and install the package:
 
```
i1 : installPackage "TotalImage"
```

The installation will go through our list of examples to make sure everything is in order. If the final line states that there are any errors, please contact us and we will help you.

## A few words about the input and output

The input is thought of as a rational map from a projective variety X to projective space. The variety X is given by an ideal `I_X` in a ring `R=QQ[x_0,...,x_n]`. The rational map is given by a sequence of polynomials `L={f_0,...,f_m}`. The input is of the form:

```
totalImage(I_X,L);
```

If the ideal I_X is ommitted, then X is assumed to be the entire space (that is I_X = (0)):

```
totalImage(L);
```

Note that we only need the coordinate ring R of the domain, and the list of polynomials L = {f_0,...,f_m} in R defining the rational map. The coordinate ring of the codomain S will be created automatically with generators `b_0,...,b_m`. That is `S=QQ[b_0,...,b_m]`. The answer will be the image of the rational map `Proj(R/I_X) - - > Proj(S)` defined by L. It is printed as a constructible set in the form of a tree of varieties in Proj(S). We simply print the vanishing ideal of each variety at each node. 

The function `totalImage` will print the output tree in a user friendly manner and it will return the basic data for the reconstruction of the tree, which is a pair of sequences: the first containing the ideals (thought of as nodes) and the other the list of edges (using the position of the nodes within the first sequence).

## Example: Cremona transformation

Let `f: P^2 - - > P^2` be the rational map defined by `[x,y,z] -> [yz,xz,xy]`. We will compute the image of `f`. In Macaulay2 write the following:

```
i2 : R = QQ[x,y,z];
i3 : L={y*z,x*z,x*y};
i4 : totalImage(L);
```

This will print the following output:

```
(2) ideal()
(1) |====ideal b_2
(0) |    |====ideal(b_2,b_0)
(0) |    |====ideal(b_2,b_1)
(1) |====ideal b_1
(0) |    |====ideal(b_1,b_0)
(0) |    |====ideal(b_2,b_1)
(1) |====ideal b_0
(0) |    |====ideal(b_2,b_0)
(0) |    |====ideal(b_1,b_0)
```

### Interpreting the printout

The numbers on the far left indicate the projective dimension of the variety corresponding to the listed ideal. 

The left and top most ideal is the `root` of our tree and describes the Zariski closure of the image. In this case, the map is dominant, hence `ideal()` is what we get.

The root has three children: `ideal b_2`, `ideal b_1`, `ideal b_0`. These are the three lines which, generically, do not belong to the image of the map `f`.

Some points on these lines can be hit however. These are then described by their children. For instance, the line `b_2=0` contains two points that which belong to the image of `f`. These are: `b_2=b_0=0` and `b_2=b_1=0`. 

Similarly, each of the other two lines contain two points in the image of `f`. Note that there us some redundancy of information, this is deliberate so that the output can be printed in the form of a tree rather than a graph.
