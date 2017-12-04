
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